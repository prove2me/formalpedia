-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_tilted_weighted_exponential_pushforward_finite
-- name    : AvramDividend.Classical.avram_p2_original_tilted_weighted_exponential_pushforward_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:45:31.761206+00:00
-- url     : https://prove2.me/theorems/7be4c17f-7468-4b33-bae9-759bfdbc6d70
-- title:
--   Original tilted fourth-weighted exponential pushforward is a finite measure
-- statement:
--   For the actual original spectrally negative Lévy source X on Ω with probability P, every time t and every nonnegative exponential tilt rho produce a finite measure by weighting P with exp(rho X_t)(exp(X_t)-1)^4 and pushing forward along exp(X_t). Finiteness follows from the already-Proved original all-tilts integrability, Mathlib's finite-measure withDensity criterion and finite pushforward theorem. This constructs a concrete positive source measure required for the small-time weighted moment method, with no compensator or coupling assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_integrable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_tilted_weighted_exponential_pushforward_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    IsFiniteMeasure
      ((P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (ρ * X.X t ω) *
          (Real.exp (X.X t ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X t ω))) := by sorry
