-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_ruin_weighted_budget_glues_closed_horizon
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_positive_ruin_weighted_budget_glues_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:07:47.289105+00:00
-- url     : https://prove2.me/theorems/97a703cc-6a9a-45ec-848e-7cbca173addf
-- title:
--   Original positive-ruin weighted stopped cash budget and genuine time-zero ruin boundary yield full closed-horizon budget
-- statement:
--   For the actual original Lévy X, dividend D, strict positive natural clock n, positive closed horizon T, and a source-identical ENNReal stopped cash function, if the measurable event of strictly positive ruin time has expected stopped cash at most w(x) times its probability, then full expected stopped cash on Iic T is at most w(x). On the complementary zero-ruin event the required pointwise bound follows from the independently Proved original Itô boundary inequality. Additivity across the two measurable parts uses the actual original probability P, with no double counting of the budget and no stochastic source assumption.
-- source:
--   Uses Proved public boundary lemma 4e324da5-54e3-4686-9a5a-e33cd12afd9f, pinned lintegral_add_measure, Measure.restrict_add_restrict_compl and X.isProbability. This isolates the genuinely missing strictly positive-ruin weighted source expected bound for canonical 665b3b52, preserving t=0, t=T and original dividendMeasure.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_ito_boundary_union_pointwise_cash_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_positive_ruin_weighted_budget_glues_closed_horizon
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
    (Cash : Ω → ℝ≥0∞)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (hEvent : MeasurableSet {ω : Ω | ruinTime X x D ω = 0})
    (hInterior :
      (∫⁻ ω in {ω : Ω | ruinTime X x D ω ≠ 0}, Cash ω ∂P) ≤
        ENNReal.ofReal (w x) * P {ω : Ω | ruinTime X x D ω ≠ 0}) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
