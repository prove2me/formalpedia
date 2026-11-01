-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_zeroCap_or_zeroHorizon
-- name    : AvramDividend.Classical.avram_wave5_05_corrected_ubv_zeroCap_or_zeroHorizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:00:32.67371+00:00
-- url     : https://prove2.me/theorems/1b8029fe-9712-44cb-9878-76ffba5fd6d3
-- title:
--   Corrected original UBV payout bound at zero cap or zero horizon
-- statement:
--   For the unchanged original spectrally negative Lévy process, its original filtration and admissible dividend Stieltjes strategy, the corrected expected discounted finite-horizon dividend bound holds whenever the cap is zero or the horizon is zero. The indispensable nonnegative verification-function boundary, initial cap and right-payment secant hypotheses are retained. This joins two independently accepted cases into one source-faithful reduction for the positive-cap positive-horizon stochastic core.
-- source:
--   Original corrected UBV target 429e17ca-5528-40b5-b593-7c03973d0706. Direct combination of accepted UUIDs b65b82f2-497b-40cf-8137-1325f2886f7f and 3858a86b-eff8-46f1-b700-7ee855dad85a; private pinned remote probe 27c831ff-04e2-4dad-bbda-c511680040d9 reached its deliberate sentinel without source errors.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zero_horizon_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zeroCap_fullHorizon_allInitialCapital


open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_corrected_ubv_zeroCap_or_zeroHorizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hBoundary : C = 0 ∨ T = 0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
