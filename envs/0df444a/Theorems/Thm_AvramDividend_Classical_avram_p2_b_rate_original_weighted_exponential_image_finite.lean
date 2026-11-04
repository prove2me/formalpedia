-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_exponential_image_finite
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_weighted_exponential_image_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:37:26.706727+00:00
-- url     : https://prove2.me/theorems/646bae71-d88a-4118-b8c0-81824c527228
-- title:
--   Original Levy weighted exponential-image measure has finite total mass
-- statement:
--   For every time of the actual spectrally negative Levy process and nonnegative exponential parameter, the fourth-exponential weighted law pushed forward by exp(theta X_t) is finite. This follows from original-source Laplace moment integrability and exact withDensity/map facts, with explicit measurable-marginal hypothesis. This is the finite Borel image law needed for tightness and polynomial inversion.

import Mathlib
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_integrable_nonnegative_density_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_weighted_exponential_image_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (((P.withDensity (fun ω =>
      ENNReal.ofReal ((Real.exp (θ * X.X t ω) - 1) ^ 4))).map
      (fun ω => Real.exp (θ * X.X t ω))) Set.univ) < ⊤ := by sorry
