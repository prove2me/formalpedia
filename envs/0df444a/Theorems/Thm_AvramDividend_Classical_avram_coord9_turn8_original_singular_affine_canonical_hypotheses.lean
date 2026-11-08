-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord9_turn8_original_singular_affine_canonical_hypotheses
-- name    : AvramDividend.Classical.avram_coord9_turn8_original_singular_affine_canonical_hypotheses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T00:21:57.191609+00:00
-- url     : https://prove2.me/theorems/abf88d78-021b-4b0b-9767-979b3e1a6231
-- title:
--   Original singular affine candidate meets all canonical HJB test hypotheses
-- statement:
--   For the actual original singular Levy triplet with zero compensated drift, the zero-extended affine candidate simultaneously satisfies canonical continuity, boundary, zero-negative-side, interior C1, global positive-reserve generator integrability, nonpositive discount-one HJB residual and derivative lower bound at every cap.
-- source:
--   Source-exact combination of Proved original a84bfed5, 835872b9, 94fba4e7, 97ead74d and 79112e24. Bundles canonical w hypotheses for the conditional singular-grid model investigation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_boundary
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_smooth
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_deriv_one
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_global_positive_reserve_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_original_generator_discount_one_le_zero
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An exact source singular Lévy triplet supplies all canonical affine
    verification test-function hypotheses at every positive reserve. -/

theorem AvramDividend.Classical.avram_coord9_turn8_original_singular_affine_canonical_hypotheses
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0) (C : ℝ≥0∞) :
    let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 + y
    ContinuousOn w (Ici 0) ∧
      0 ≤ w 0 ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - 1 * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) := by sorry
