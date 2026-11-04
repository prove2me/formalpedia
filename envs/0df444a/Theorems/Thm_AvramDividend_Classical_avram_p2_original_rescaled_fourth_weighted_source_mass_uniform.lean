-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_fourth_weighted_source_mass_uniform
-- name    : AvramDividend.Classical.avram_p2_original_rescaled_fourth_weighted_source_mass_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:38:44.448213+00:00
-- url     : https://prove2.me/theorems/994b1544-e403-4dfc-8387-2042ae03cca3
-- title:
--   Rescaled original fourth-weighted Lévy source mass is uniformly bounded near time zero
-- statement:
--   For the same original spectrally negative Lévy process and probability space, the finite fourth-weighted mass of exp(X_h), divided by positive time h, has a finite uniform upper bound for all sufficiently small h. This supplies the zeroth-moment uniform-mass premise for tightness of original weighted exponential image measures, using a previously proved source O(h) bound; it assumes no jump-rate or compensator identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_tilted_weighted_ennreal_linear_smalltime_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_rescaled_fourth_weighted_source_mass_uniform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (ENNReal.ofReal h)⁻¹ *
          (∫⁻ ω, ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) ∂P) ≤
        ENNReal.ofReal C := by sorry
