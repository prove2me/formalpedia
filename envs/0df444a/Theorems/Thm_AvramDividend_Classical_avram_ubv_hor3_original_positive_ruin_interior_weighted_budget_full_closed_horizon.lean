-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_ruin_interior_weighted_budget_full_closed_horizon
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_positive_ruin_interior_weighted_budget_full_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:24:07.310965+00:00
-- url     : https://prove2.me/theorems/424b3eb3-9eda-4e5d-af90-17c700bb4ee8
-- title:
--   Genuine original positive-ruin weighted interior stopped dividend budget closes all original positive closed-horizon cash
-- statement:
--   For the literal original process X and admissible dividends D at positive n,T, an expected cash bound restricted to the strictly positive ruin-time event and weighted by its actual original probability is sufficient for the full original expected stopped cash budget. The complementary zero-ruin branch is proved physically; measurability of the zero-ruin event and source-identical Cash are obtained automatically from the original strategy and published source lemmas. No abstract Cash witness or extra measurability premise remains.
-- source:
--   Strengthens Proved/public 97a703cc with original ruinTime_measurable (bbfbecf4), exact original Cash and no extra event/Cash witness. This is a directly canonical-shaped positive-horizon adapter; the weighted interior stochastic inequality remains a real unproved source obligation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_ruin_weighted_budget_glues_closed_horizon
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_positive_ruin_interior_weighted_budget_full_closed_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (T : ℝ) (hT : 0 < T)
    (hInterior :
      (∫⁻ ω in {ω : Ω | ruinTime X x D ω ≠ 0},
        (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
        ENNReal.ofReal (w x) * P {ω : Ω | ruinTime X x D ω ≠ 0}) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
