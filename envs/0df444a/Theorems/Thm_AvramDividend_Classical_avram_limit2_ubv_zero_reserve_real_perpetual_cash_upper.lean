-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_zero_reserve_real_perpetual_cash_upper
-- name    : AvramDividend.Classical.avram_limit2_ubv_zero_reserve_real_perpetual_cash_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:37:52.20748+00:00
-- url     : https://prove2.me/theorems/09801b16-dc07-4dd6-a082-280e6dbb2429
-- title:
--   Actual UBV zero-reserve capped strategy has integrable real perpetual Stieltjes cash bounded by HJB boundary value
-- statement:
--   For the original unbounded-variation Lévy process at exactly zero initial capital, the already Proved canonical HJB zero-start theorem bounds valueFunctionLe X q C 0 by ENNReal.ofReal (w 0). A genuine capped admissible strategy D is one member of that actual iSup, yielding its dividendValue bound. Since ofReal(w 0) is finite, the Proved original perpetual signed Stieltjes theorem gives L1 integrability of the untruncated real discounted dividend-measure payout on paymentTimes(ruinTime) and exact ENNReal.ofReal expected-real-cash equality. Pinned ENNReal.ofReal_le_ofReal_iff transfers the bound to the real mean. This handles x=0 without assuming a strictly positive reserve or a P4 Itô–Meyer martingale witness. Initial and terminal payment atoms, ruin stopping, probability P and original process remain unchanged.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_capped_valueFunctionLe_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ubv_zero_reserve_real_perpetual_cash_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X 0 D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X 0 D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w 0 := by sorry
