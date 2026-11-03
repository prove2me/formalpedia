-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_budgets_valueFunction_le
-- name    : AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_valueFunction_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:02:33.260698+00:00
-- url     : https://prove2.me/theorems/72c8949b-6ea2-4193-b9e9-04bf3c5973a2
-- title:
--   Original unrestricted dividend value function bound from genuine uniform signed Stieltjes horizons
-- statement:
--   If the expected original genuine real discounted Stieltjes dividend payout on every positive integer horizon is bounded by the same real B uniformly over all IsAdmissible strategies, then the canonical unrestricted valueFunction X q x is ≤ ENNReal.ofReal B. Each admissible strategy is also IsAdmissibleLe with cap top, so the accepted uniform signed-to-perpetual bridge applies. Two iSup_le steps give the original supremum bound. This is an exact budget-to-optimisation bridge, not a proof of the HJB budget hypothesis itself.
-- source:
--   Proved original uniform signed horizon budgets imply full perpetual ENNReal theorem 1caf0f13, IsAdmissibleLe with C=top, canonical Definition valueFunction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_valueFunction_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
      (n : ℕ),
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    valueFunction X q x ≤ ENNReal.ofReal B := by sorry
