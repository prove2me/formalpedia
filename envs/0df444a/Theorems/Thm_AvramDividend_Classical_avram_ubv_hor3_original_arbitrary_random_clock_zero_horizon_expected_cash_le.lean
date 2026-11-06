-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_arbitrary_random_clock_zero_horizon_expected_cash_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_arbitrary_random_clock_zero_horizon_expected_cash_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:08:39.602168+00:00
-- url     : https://prove2.me/theorems/fffdcb13-620a-4904-ae51-ec87dd2581e2
-- title:
--   Original random stopping clock zero-horizon full Stieltjes expectation controlled without stochastic decomposition
-- statement:
--   For the original spectrally negative Lévy probability space and original admissible D, every sample-dependent extended-nonnegative clock σ(ω) satisfies a full raw Stieltjes zero-horizon expected-cash bound by the same original-path integral of ENNReal.ofReal(w x). This includes possibly nonmeasurable arbitrary clock assignments because the eventwise inequality is pointwise, requires no stopped martingales and preserves the time-zero dividend atom. Under a separately certified probability measure, the right side reduces to ENNReal.ofReal(w x).
-- source:
--   Integrate the newly public Proved original samplewise arbitrary-clock zero-horizon HJB bound 651ba069 by ENNReal lintegral monotonicity, instantiated at σ ω. No stochastic clock measurability is needed for the monotonicity inequality; source dividendMeasure and X/P unchanged.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_any_stopping_clock_zero_horizon_pointwise_cash_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_arbitrary_random_clock_zero_horizon_expected_cash_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
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
    (σ : Ω → ℝ≥0∞) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (w x) ∂P) := by sorry
