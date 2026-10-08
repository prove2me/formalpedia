-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_uniform_strategy_bound
-- name    : AvramDividend.Classical.local_verification_uniform_strategy_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:42:45.254869+00:00
-- url     : https://prove2.me/theorems/96ff5551-5a42-4c80-9f9a-ca104ee3d85e
-- title:
--   Reduce the full discounted dividend value bound for every capped strategy to the BV/UBV truncated stochastic lemmas and random payout measurability
-- statement:
--   For any capped admissible dividend strategy, the original local-verification hypotheses imply dividendValue≤ofReal(w x). The proof combines the proved HJB maximum decomposition, the proved derivation of w(U_t)≥0 before ruin, the appropriate bounded- or unbounded-variation truncated stochastic payout estimate for every finite natural horizon, and the monotone-convergence bridge from truncated payout expectations to the full value. The remaining independently difficult leaves are the BV/UBV stochastic Itô-Dynkin inequalities and measurable random Stieltjes integrals. This theorem provides an exact, checkable reduction of the substantive root obligation.
-- source:
--   Children local_verification_hjb_implies_components, local_verification_stochastic_test_nonneg, admissible_cap_truncated_bv_stochastic_bound, admissible_cap_truncated_ubv_stochastic_bound, truncated_dividend_payoff_measurable, dividendValue_le_of_truncated_bound_measurable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_uniform_strategy_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
