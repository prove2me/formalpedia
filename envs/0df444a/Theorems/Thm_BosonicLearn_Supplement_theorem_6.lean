-- Prove2me | Theorems.Thm_BosonicLearn_Supplement_theorem_6
-- name    : BosonicLearn.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:02:49.356974+00:00
-- url     : https://prove2.me/theorems/496a7a26-89d3-4ad0-b76a-e1caf204b321
-- title:
--   Theorem 6 — non-adaptive single-copy learning of cold passive Gaussian states needs $\Omega(n^3/\varepsilon^2)$ copies, even with known symplectic spectrum
-- statement:
--   Work on $n$ bosonic modes, with Gaussian states $\rho(\mu,\Sigma)$ in the convention where the vacuum has covariance $\Sigma=\tfrac12 I_{2n}$. A **single-copy non-adaptive scheme** on $N$ copies measures each copy separately with a POVM $M_1,\dots,M_N$ fixed in advance (not depending on earlier outcomes; non-Gaussian POVMs with arbitrary outcome spaces are allowed), followed by any randomized estimator. Learning to precision $\varepsilon$ means $\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon$.
--
--   There are $n_0\in\mathbb N$ and $c>0$ such that for every $n\ge n_0$ and every $0<\varepsilon\le 0.01$:
--
--   1. any single-copy non-adaptive scheme that learns every passive Gaussian state $\rho(0,\Sigma)$ with
--   $$\frac1n I\ \preceq\ \Sigma-\frac12 I\ \preceq\ \frac2n I$$
--   to precision $\varepsilon$ with probability at least $2/3$ uses $N\ge c\,n^3/\varepsilon^2$ copies;
--   2. there are $\nu_1,\dots,\nu_n\in[\tfrac1n,\tfrac2n]$ such that the same bound $N\ge c\,n^3/\varepsilon^2$ holds for every single-copy non-adaptive scheme (which may depend on $\nu$) that only needs to learn the states of this class whose symplectic eigenvalues are $\tfrac12+\nu_1,\dots,\tfrac12+\nu_n$.
--
--   So the cubic single-copy lower bound for cold states survives even when the spectrum of the state is known in advance, at least for non-adaptive schemes; heterodyne measurement attains it.
--
--   **Formalization Note** "Sufficiently large $n$" and $\Omega(\cdot)$ are read as $n_0$ and $c$ chosen before $n$ and $\varepsilon$. A non-adaptive scheme is a base `AdaptiveScheme` whose round-$t$ POVM does not depend on the earlier outcomes. For a passive state, $\Sigma-\tfrac12 I$ is the realification of the Hermitian occupation matrix, so the eigenvalues of $\Sigma$ are its symplectic eigenvalues, each twice; the known spectrum is written $\operatorname{charpoly}\Sigma=\prod_j\big(X-(\tfrac12+\nu_j)\big)^2$.
--
--   Differences from the source:
--   - reading: "For sufficiently large n", N = Ω(n³/ε²) → ∃ n₀, c > 0 before n and ε, and N ≥ c·n³/ε²; reason: the stronger of the two readings (n₀ uniform in ε ∈ (0, 0.01]); the proof's largeness conditions (the 2^{Θ(n²)} packing and the odd-n padding with ξ = 66ε ≤ 0.66) do not depend on ε.
--   - reading: "This holds even if the symplectic eigenvalues of the state are a priori known" → ∃ ν ∈ [1/n, 2/n]ⁿ (after n and ε, before the scheme) such that the bound holds for the subclass with symplectic eigenvalues 1/2 + ν_j; reason: the universal reading is false (all ν_j equal gives a single thermal state, learnable with no copies); the proof fixes one spectrum (Eq. (150)).
--   - encoding: symplectic eigenvalues of a passive Gaussian state → charpoly Σ = ∏_j (X − (1/2 + ν_j))²; reason: for passive states the eigenvalues of Σ are the symplectic eigenvalues, each with multiplicity two.
--   - encoding: single-copy non-adaptive scheme → AdaptiveScheme with S.povm t x = S.povm t y for all t, x, y; reason: fixed POVMs, one per copy; the estimator stays an arbitrary Markov kernel.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 6, p. 46; Eq. (150), p. 46

import Mathlib
import Definitions.Def_BosonicLearn_successProb
import Definitions.Def_BosonicLearn_IsPassive

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn.Supplement

/-- **Theorem 6 (Non-adaptive single-copy lower bound, even with known symplectic spectrum).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705,
Theorem 6, p. 46: "For sufficiently large n, any single-copy non-adaptive scheme that can learn any n-mode passive
Gaussian state ρ(0, Σ), with the promise that (1/n) I ≤ Σ − (1/2) I ≤ (2/n) I, to trace distance precision
0 < ε ≤ 0.01 with at least 2/3 probability requires N = Ω(n³/ε²) copies. This holds even if the symplectic
eigenvalues of the state are a priori known."

There are `n₀` and `c > 0` such that for every `n ≥ n₀` and `ε ∈ (0, 0.01]`:
1. every non-adaptive single-copy scheme on `N` copies (the POVM of each round does not depend on the earlier
   outcomes) with any measurable outcome space, with any (randomized) estimator, that learns every passive Gaussian
   state `ρ(0, Σ)` with `(1/n) I ⪯ Σ − ½ I ⪯ (2/n) I` to trace distance `ε` with probability at least `2/3` has
   `N ≥ c n³/ε²`;
2. there is a spectrum `ν₁, …, νₙ ∈ [1/n, 2/n]` such that the same bound holds for schemes that need only learn the
   passive states of this class whose symplectic eigenvalues are `½ + ν₁, …, ½ + νₙ` (the scheme and the estimator
   may depend on `ν`).

**Formalization Note.** "Sufficiently large n" and `Ω(·)` are read as `n₀` and `c` chosen before `n` and `ε`
(uniform in `ε`). "Known symplectic eigenvalues" is existential in the spectrum: with all `νⱼ` equal the class is a
single thermal state, so it cannot be universal. For a passive Gaussian state `Σ − ½ I` is the realification of the
Hermitian occupation matrix `N = (⟨â_i† â_j⟩)`, so its symplectic eigenvalues `½ + νⱼ` are the eigenvalues of `Σ`,
each twice; the known spectrum is expressed as `charpoly Σ = ∏ⱼ (X − (½ + νⱼ))²`. The covariance is the paper's
(vacuum `½ I`), see `IsGaussianState`. -/
theorem theorem_6 :
    ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 →
      (∀ (N : ℕ) (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O)
        (est : Kernel (Fin N → O) (State (Occupation (Fin n)))), IsMarkovKernel est →
        (∀ (t : Fin N) (x y : Fin t → O), S.povm t x = S.povm t y) →
        (∀ ρ : State (Occupation (Fin n)), IsPassive ρ →
            (∃ Sg : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, IsGaussianState ρ 0 Sg ∧
              (Sg - (1 / 2 + 1 / (n : ℝ)) •
                (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef ∧
              ((1 / 2 + 2 / (n : ℝ)) •
                (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - Sg).PosSemidef) →
            ENNReal.ofReal (2 / 3) ≤ successProb S est ρ.coefficients ε) →
        c * ((n : ℝ) ^ 3 / ε ^ 2) ≤ N) ∧
      ∃ ν : Fin n → ℝ, (∀ j, 1 / (n : ℝ) ≤ ν j ∧ ν j ≤ 2 / (n : ℝ)) ∧
        ∀ (N : ℕ) (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O)
          (est : Kernel (Fin N → O) (State (Occupation (Fin n)))), IsMarkovKernel est →
          (∀ (t : Fin N) (x y : Fin t → O), S.povm t x = S.povm t y) →
          (∀ ρ : State (Occupation (Fin n)), IsPassive ρ →
              (∃ Sg : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, IsGaussianState ρ 0 Sg ∧
                (Sg - (1 / 2 + 1 / (n : ℝ)) •
                  (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef ∧
                ((1 / 2 + 2 / (n : ℝ)) •
                  (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - Sg).PosSemidef ∧
                Sg.charpoly = ∏ j, (Polynomial.X - Polynomial.C (1 / 2 + ν j)) ^ 2) →
              ENNReal.ofReal (2 / 3) ≤ successProb S est ρ.coefficients ε) →
          c * ((n : ℝ) ^ 3 / ε ^ 2) ≤ N := by sorry

end BosonicLearn.Supplement
