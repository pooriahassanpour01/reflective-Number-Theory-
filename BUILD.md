# Build Instructions for ZRAP (Reflective Number Theory Formalization)

This project formalizes the Reflective Number Theory framework in **Lean 4**, including the ZRAP (Zeta Reflective Abolishment Protocol) theorem suite. All theorems have been mechanically verified in Lean 4.25.0.

## Prerequisites

- **Lean 4.25.0** (or compatible version)
- **Lake** (Lean's build system) — typically installed with Lean
- **Git** for version control
- **Internet connection** (for downloading mathlib4 and dependencies)

## Installation

### Step 1: Install Lean 4 and Lake

We recommend using **elan** (the Lean Version Manager):

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
```

After installation, restart your terminal or add elan to your PATH:

```bash
export PATH="$HOME/.elan/bin:$PATH"
```

### Step 2: Clone the Repository

```bash
git clone https://github.com/pooriahassanpour01/reflective-Number-Theory-.git
cd reflective-Number-Theory-
```

### Step 3: Set the Lean Toolchain

The project uses Lean 4.25.0, specified in `lean-toolchain`. elan will automatically use this version:

```bash
elan default leanprover/lean4:v4.25.0
```

Verify the toolchain:

```bash
lean --version
lake --version
```

## Building the Project

### Clean Build

```bash
cd /path/to/reflective-Number-Theory-
lake build
```

This will:
1. Download and cache mathlib4 dependencies
2. Compile all Lean files in `ReflectiveNumberTheory/`
3. Generate compiled `.olean` (Lean object) files

**Note:** First build may take **10–30 minutes** due to mathlib4 compilation. Subsequent builds are much faster.

### Cache Optimization

If the build complains about missing `.olean` files, download the precompiled cache:

```bash
lake exe cache get
```

This significantly speeds up subsequent builds.

### Clean Rebuild

To rebuild everything from scratch:

```bash
rm -rf .lake/build
lake build
```

## Project Structure

```
.
├── ReflectiveNumberTheory.lean         # Root module (imports all submodules)
├── ReflectiveNumberTheory/
│   ├── Basic.lean                      # Core RNT definitions (Anchor, R-map, etc.)
│   ├── RiemannZeta.lean                # Zeta function and functional equation
│   ├── Uniqueness.lean                 # Properties of factorization uniqueness
│   └── ZRAPFormalization.lean          # ZRAP main theorems and dichotomy proofs
├── Main.lean                           # Executable entry point
├── lakefile.lean                       # Lake build configuration (Lean)
├── lakefile.toml                       # Lake build configuration (TOML)
├── lean-toolchain                      # Lean 4 version specification
└── lake-manifest.json                  # Locked versions of dependencies
```

## Key Modules

- **ReflectiveNumberTheory.Basic**: Defines the Anchor Principle, the reflective map R, and RNT-Primes
- **ReflectiveNumberTheory.RiemannZeta**: Riemann zeta function, completed zeta, and functional equations
- **ReflectiveNumberTheory.Uniqueness**: Theorems on factorization uniqueness and Euler product collapse
- **ReflectiveNumberTheory.ZRAPFormalization**: Complete ZRAP theorem suite, including:
  - `one_is_RNTPrime`: 1 is a prime in the RNT framework
  - `two_not_RNTPrime`: 2 is excluded from RNT-Primes
  - `RNT_factorization_non_unique`: Non-unique factorization demonstration
  - `riemann_hypothesis_meaningless_under_RNT`: RH becomes structurally undefined
  - `compulsion_to_critical_line`: If zeta survives, its zeros must lie on Re(s) = 1/2

## Type-Checking Without Building

To type-check a specific file without full compilation:

```bash
lake env lean ReflectiveNumberTheory/ZRAPFormalization.lean
```

This checks the file against the lake-managed environment but does not produce `.olean` files.

## Development in VS Code

1. Install the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) for VS Code
2. Open the project folder
3. Lean should automatically activate, showing type errors inline
4. Hover over theorems/definitions to see their signatures and documentation

## Troubleshooting

### Build hangs or is slow

- First build is expected to take 10–30 minutes due to mathlib4 compilation
- Ensure internet connectivity for downloading dependencies
- Check available disk space (mathlib4 + compiled artifacts ≈ 5–10 GB)

### "unknown module prefix 'Mathlib'" errors

- Run `lake exe cache get` to ensure mathlib4 is properly cached
- Verify Lean version: `lean --version` (should be v4.25.0)

### Module not found errors

- Ensure all files are in `ReflectiveNumberTheory/` directory
- Check that imports use full paths: `import ReflectiveNumberTheory.Basic` (not just `import Basic`)
- Clear cache and rebuild: `rm -rf .lake/build && lake build`

### Out of memory during build

- Reduce parallelism: `lake build -- -j1`
- On resource-constrained systems, consider using incremental builds

## Verification Status

✅ **All theorems fully verified in Lean 4 (no axioms, no sorry, no admit)**

The code compiles cleanly without:
- `axiom` declarations (no unproven assumptions)
- `sorry` placeholders
- `admit` tactics

This provides **mechanically-certified proof** of the ZRAP framework's theorems.

## References

- **Lean 4 Documentation**: https://lean-lang.org/
- **Mathlib4**: https://github.com/leanprover-community/mathlib4
- **Lake Documentation**: https://github.com/leanprover/lake

## Contributing

Contributions are welcome! To extend or verify additional theorems:

1. Fork the repository
2. Create a feature branch
3. Add your theorems to the appropriate module
4. Run `lake build` to verify compilation
5. Submit a pull request with a description of your changes

## License

See `LICENSE` file for details.
