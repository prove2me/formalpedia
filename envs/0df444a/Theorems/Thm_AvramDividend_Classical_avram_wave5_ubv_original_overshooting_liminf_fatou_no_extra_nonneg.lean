-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_overshooting_liminf_fatou_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_overshooting_liminf_fatou_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:28:32.844571+00:00
-- url     : https://prove2.me/theorems/0fd62ba3-85ac-4c84-a50c-8903a2c8a2cb
-- title:
--   Original UBV Fatou from nonmonotone localisers whose liminf merely covers ruin
-- statement:
--   For the actual source X and admissible D, a sequence of measurable random clocks may be nonmonotone and may overshoot ruin. It suffices that its tail-infimum limit is at least the genuine ruinTime almost surely, rather than exactly equal to ruinTime. Clip each clock at the actual ruin endpoint, preserving measurability and reducing the expected nonnegative Stieltjes payout. The clipped clocks have liminf equal to ruinTime by lattice distributivity. Apply the Proved nonmonotone original-source Fatou theorem. This holds with 0≤w(0), all finite/infinite endpoints, the unchanged source filtration, no additional smoothness, bounded variation or boundary hypothesis. The per-clock stochastic budget remains an explicit premise.
-- source:
--   Corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706; accepted nonmonotone Fatou b7105a08-8cdc-4cb9-a67c-5eff0eb612fd and paymentTimes monotonicity 021cfe05-e7e2-40b3-acd0-0850489ea100.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_overshooting_liminf_fatou_no_extra_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (τ : ℕ → Ω → ℝ≥0∞) (hτmeas : ∀ n, Measurable (τ n))
    (hτliminfLowerAE : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
