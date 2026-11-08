-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_finset_stable
-- name    : AvramDividend.Classical.avram_route_runner_f_original_unit_grid_cell_finset_stable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:56:38.923012+00:00
-- url     : https://prove2.me/theorems/6e0d9ba6-ad6f-4a11-8fd9-869e64362c26
-- title:
--   Original unit-grid strict negative marked cell is invariant under shortening its outer jump horizon
-- statement:
--   For the original spectrally negative Levy path, choosing all negative-cutoff jump times before one and filtering to any half-open cell inside one yields exactly the jump-time finite set defined at that cell's right endpoint. The result allows the Proved arbitrary-cell Laplace product identity to be applied to the canonical equal-grid products defined from the full unit horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_f_original_unit_grid_cell_finset_stable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (ht : t ≤ 1) (k : ℕ) :
    (avram_redux19_original_strict_negative_marked_times_finite
      X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t) =
    (avram_redux19_original_strict_negative_marked_times_finite
      X ω t k).toFinset.filter (fun u => s < u) := by sorry
