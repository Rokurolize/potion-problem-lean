# Potion Problem - Lean 4 Formalization

A complete Lean 4 formalization proving that E[τ] = e for the Potion Problem (媚薬問題).

## Main Result

**Theorem**: The expected number of doses required equals Euler's number e.

```lean
theorem main_theorem : expected_hitting_time = exp 1
```

Status: ✅ **Proven with ZERO sorries** in the core modules.

## Build Instructions

```bash
lake build
```

## Project Structure

```
├── PotionProblem.lean          # Library entry point
├── PotionProblem/
│   ├── Basic.lean              # Core PMF definition
│   ├── FactorialSeries.lean    # Factorial series convergence  
│   ├── ProbabilityFoundations.lean  # PMF properties
│   ├── SeriesAnalysis.lean     # Telescoping series proof
│   ├── IrwinHallTheory.lean    # Geometric interpretation (4 sorries)
│   └── Main.lean               # Main theorem
├── test/                       # Test files
├── lakefile.toml              # Build configuration
├── lean-toolchain             # Lean version (v4.22.0-rc4)
└── LICENSE                    # MIT License
```

## Mathematical Background

Starting from sensitivity 1, each dose increases it by a uniform random amount in [0,1). The problem asks for the expected number of doses until sensitivity first exceeds 2.

The answer is exactly e, arising from the telescoping series:
- P(τ = n) = (n-1)/n! for n ≥ 2
- E[τ] = Σ(n=2 to ∞) n·P(τ=n) = e

## License

MIT License - see LICENSE file for details.