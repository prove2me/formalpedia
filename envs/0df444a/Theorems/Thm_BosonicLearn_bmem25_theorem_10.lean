-- Prove2me | Theorems.Thm_BosonicLearn_bmem25_theorem_10
-- name    : BosonicLearn.bmem25_theorem_10
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:34:22.504534+00:00
-- url     : https://prove2.me/theorems/864c1313-9a70-4a56-b7e0-29e7e72109d2
-- title:
--   [BMEM25, Theorem 10] as used in Corollary 19 — $O(n^3/\epsilon^2)$ heterodyne copies without the vacuum gap
-- statement:
--   For every failure probability $\delta\in(0,1)$ there is a constant $C_\delta$ such that for every $n$ and $\epsilon>0$ there are $N\le C_\delta\,n^3/\epsilon^2$ and an estimator of $N$ independent heterodyne outcomes which, for every $n$-mode Gaussian state $\rho(\mu,\Sigma)$ with $\Sigma\succ\tfrac12I$, satisfies
--
--   $$\Pr\Big[\tfrac12\|\hat\rho-\rho(\mu,\Sigma)\|_1\le\epsilon\Big]\ge1-\delta .$$
--
--   One protocol serves every vacuum gap $\nu>0$ at once. Together with Theorem 8 it gives Corollary 19. The paper imports it from [BMEM25].
--
--   Differences from the source:
--   - reading: "applies without using the vacuum-gap promise", for the states of Corollary 19 → all Gaussian states with Σ − ½I positive definite, one protocol for all ν > 0; reason: the union of the promise classes over ν > 0, which Corollary 19 needs; p. 8 restricts to ν > 0 and footnote 4 (p. 7) gives squeezed states an energy factor
--   - reading: "for constant failure probability" (Corollary 19) → for every δ ∈ (0, 1), the constant depending on δ; reason: the proof of Theorem 3 uses δ = 1/3
--   - encoding: O(·) and "there is a … protocol" → ∃ C > 0 before every other variable; N and the estimator chosen before the state; reason: the constant is universal and the protocol must work for every state of the class
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, proof of Corollary 19 (unnumbered display), p. 65

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneSuccess
import Definitions.Def_BosonicLearn_IsGaussianState
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **[BMEM25, Theorem 10] as used in the proof of Corollary 19: `O(n³/ϵ²)` heterodyne copies.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, proof of Corollary 19 (unnumbered display), p. 65: "On the other hand, the general heterodyne tomography
bound of [BMEM25, Theorem 10] applies without using the vacuum-gap promise and gives N = O(n³/ϵ²)."

For every failure probability `δ ∈ (0, 1)` there is a constant `C_δ` such that for every `n` and `ϵ > 0` there are
`N ≤ C_δ n³/ϵ²` and a measurable estimator of `N` heterodyne outcomes that learns every `n`-mode Gaussian state
whose covariance satisfies `Σ ≻ ½I` to trace distance `ϵ` with probability at least `1 − δ`.

**Formalization Note.** The class is all Gaussian states with `Σ − ½I` positive definite, the union of the
promise classes over `ν > 0`, with one protocol for all of them; see the Differences list. -/
theorem bmem25_theorem_10 :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ϵ : ℝ), 0 < ϵ →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) ^ 3 / ϵ ^ 2) ∧
        ∃ est : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → State (Occupation (Fin n)),
          Measurable est ∧
          ∀ ρ : State (Occupation (Fin n)),
            (∃ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
              IsGaussianState ρ μ S ∧
                (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosDef) →
            ENNReal.ofReal (1 - δ) ≤ heterodyneSuccess N est ρ ϵ := by sorry

end BosonicLearn
