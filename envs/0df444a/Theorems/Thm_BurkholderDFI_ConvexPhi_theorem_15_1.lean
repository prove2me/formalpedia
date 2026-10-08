-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_theorem_15_1
-- name    : BurkholderDFI.ConvexPhi.theorem_15_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:25.782047+00:00
-- url     : https://prove2.me/theorems/6cf055bd-4068-4f3d-8dd0-a3672a7b88d2
-- title:
--   Theorem 15.1 — two-sided convex Φ inequality for martingales
-- statement:
--   Let $f$ be a real martingale and let $\Phi$ be convex, nondecreasing, continuous, zero at zero, and of moderate growth $\Phi(2x)\le c\Phi(x)$. With $S(f)$ its square function and $f^*$ its maximal function, there are positive constants $C_1,C_2$ depending only on $c$ such that
--   $$
--   C_1E\Phi(S(f))\le E\Phi(f^*)\le C_2E\Phi(S(f)).
--   $$
--   For $\Phi(x)=x$, this includes Davis's $L^1$ comparison; convex powers $\Phi(x)=x^p$ give the $p\ge1$ cases. The theorem is the mission's goal.
--
--   **Formalization Note** The constants are chosen before the probability space, martingale, and $\Phi$. The nonnegative quantities and expectations may be infinite. Mathlib's martingale includes an index-zero extension, whereas the displayed square and maximal functions use only positive indices and the paper's convention $f_0=0$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 15.1, p. 33

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 15.1, p. 33: the two-sided convex Φ inequality. -/
theorem theorem_15_1 (c : ℝ≥0) :
    ∃ C₁ C₂ : ℝ≥0, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c → BurkholderDFI.SquareFnLp.IsConvexPhi Φ →
          (C₁ : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.sqFn f ω) ∂P ≤ ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P ∧
          ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P ≤ (C₂ : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.sqFn f ω) ∂P := by sorry
end BurkholderDFI.ConvexPhi
