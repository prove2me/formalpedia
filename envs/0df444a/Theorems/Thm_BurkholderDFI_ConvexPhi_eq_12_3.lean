-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_eq_12_3
-- name    : BurkholderDFI.ConvexPhi.eq_12_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:08.586615+00:00
-- url     : https://prove2.me/theorems/3dc3c3f9-04c4-47e3-9d24-907ab852cd89
-- title:
--   (12.3) — good-λ inequality with predictable jump control
-- statement:
--   Let $f$ be a martingale and let $w_k$ be $\mathcal A_{k-1}$-measurable with $|d_k|\le w_k$ almost surely, for $k\ge1$. Write $w^*=\sup_{k\ge1}w_k$. For $\beta>1$, $0<\delta<\beta-1$, and $\lambda>0$,
--   $$
--   P(f^*>\beta\lambda,\ S(f)\vee w^*\le\delta\lambda)
--   \le\frac{2\delta^2}{(\beta-\delta-1)^2}P(f^*>\lambda).
--   $$
--   This is the distribution estimate used for (12.1).
--
--   **Formalization Note** The predictable bound is almost everywhere for each index; the displayed event is formed from the extended nonnegative square and maximal functions. The parameter restriction makes the denominator positive.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (12.3), p. 31

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (12.3), p. 31: predictable jump control gives a good-λ estimate. -/
theorem eq_12_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (w : ℕ → Ω → ℝ)
    (hw_pred : ∀ k, 1 ≤ k → Measurable[ℱ (k - 1)] (w k))
    (hw_bound : ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, |BurkholderDFI.SquareFnLp.dseq f k ω| ≤ w k ω)
    (β δ l : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < β - 1) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.maxFn f ω ∧
      max (BurkholderDFI.SquareFnLp.sqFn f ω) (BurkholderDFI.SquareFnLp.maxFn w ω) ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (2 * δ ^ 2 / (β - δ - 1) ^ 2) *
        P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} := by sorry
end BurkholderDFI.ConvexPhi
