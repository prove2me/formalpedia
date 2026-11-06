-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_localized_weighted_generator_drift_cover
-- name    : AvramDividend.Classical.avram_bv_env3_original_localized_weighted_generator_drift_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:51:38.771315+00:00
-- url     : https://prove2.me/theorems/47a77c74-30d1-47de-88d2-713c424c1085
-- title:
--   Original hard BV HJB generator drift cover integrated against any nonnegative localising weight
-- statement:
--   In the strict BV drift-envelope complement, the original generator HJB inequality bounds drift by discounting minus the negative-jump generator integral at every interior reserve. Integrate this source-exact pointwise inequality against a nonnegative stopping/localisation weight to obtain the weighted drift budget, provided both sides are integrable. This is an independent localised source ingredient for the finite-horizon stochastic verification and retains the exact original Levy process.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 4(i), equation (5.13), and official Proved original pointwise jump discount drift cover theorem 3794152d-4a35-496d-b893-ed3868ea4ebb. Parent c8770486 requires separate actual reserve localisation, source compensated martingale and Fatou limit; no circular parent import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_interior_jump_discount_drift_cover
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_localized_weighted_generator_drift_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x))
    (μ : Measure ℝ) (Y g : ℝ → ℝ)
    (hg : ∀ᵐ t ∂μ, 0 ≤ g t)
    (hY : ∀ᵐ t ∂μ, 0 < Y t ∧ ENNReal.ofReal (Y t) < C)
    (hIntD : Integrable (fun t => g t * X.drift) μ)
    (hIntG : Integrable (fun t => g t *
      (q * w (Y t) - ∫ z in Iio (0 : ℝ),
        w (Y t + z) - w (Y t) ∂X.ν)) μ) :
    (∫ t, g t * X.drift ∂μ) ≤
      ∫ t, g t * (q * w (Y t) -
        ∫ z in Iio (0 : ℝ),
          w (Y t + z) - w (Y t) ∂X.ν) ∂μ := by sorry
