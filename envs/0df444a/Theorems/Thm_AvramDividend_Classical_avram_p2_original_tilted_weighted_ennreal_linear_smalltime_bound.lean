-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_tilted_weighted_ennreal_linear_smalltime_bound
-- name    : AvramDividend.Classical.avram_p2_original_tilted_weighted_ennreal_linear_smalltime_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:00:53.905743+00:00
-- url     : https://prove2.me/theorems/9d4b1b20-d4c9-447a-ade8-cdd9a16765cf
-- title:
--   Original tilted fourth-weighted ENNReal masses are O(h) for all nonnegative rates
-- statement:
--   On the unchanged original spectrally negative Lévy sample space for any nonnegative exponential tilt rho, the ENNReal lintegral of exp(rho X_h)(exp X_h-1)^4 is at most ENNReal.ofReal(C h) for all sufficiently small positive h, with positive finite C. Uses the Proved original tilted real integral O(h) rate, Proved integrability and Mathlib's equality of the ENNReal lintegral with ofReal of a nonnegative real integral. This transfers the genuine original small-time transform bounds into the ENNReal finite-measure mass bounds required for Prokhorov tightness. No Poisson replacement or stronger assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_linear_smalltime_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_tilted_weighted_ennreal_linear_smalltime_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (∫⁻ ω, ENNReal.ofReal (Real.exp (ρ * X.X (Real.toNNReal h) ω) *
          (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) ∂P) ≤
          ENNReal.ofReal (C * h) := by sorry
