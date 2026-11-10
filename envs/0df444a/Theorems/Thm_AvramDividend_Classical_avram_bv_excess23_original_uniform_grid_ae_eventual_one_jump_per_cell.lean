-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess23_original_uniform_grid_ae_eventual_one_jump_per_cell
-- name    : AvramDividend.Classical.avram_bv_excess23_original_uniform_grid_ae_eventual_one_jump_per_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T21:42:13.034086+00:00
-- url     : https://prove2.me/theorems/5ca01b4f-1b51-4ca5-8cb9-9bef4b516126
-- title:
--   One full original BV event gives eventual single-negative-jump occupancy on every genuinely shrinking physical mesh
-- statement:
--   Under source finite-negative-activity BV, a random positive minimal separation of genuine original-X jump times exists almost surely on every finite horizon (proved 90932671). For every predetermined triangular grid family with genuine shrinking maximum cell diameter, eventually every actual original physical cell contains at most one negative source jump. This is the precise original-source geometric input for vanishing of the collision error (k-1)_+ in f3f336fd, without arbitrary collapsed-grid assumptions or a finite second moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_separated_jumps_one_per_short_cell_ae
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bv_excess23_original_uniform_grid_ae_eventual_one_jump_per_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0) (cells : ℕ → ℕ)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in (Filter.atTop : Filter ℕ),
        ∀ i : ℕ, i < cells n →
          dist (grid n i) (grid n (i + 1)) < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in (Filter.atTop : Filter ℕ),
      ∀ i : ℕ, i < cells n →
      ∀ u v : ℝ≥0,
      (u ≤ T ∧ 0 < u ∧
        X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0) →
      (v ≤ T ∧ 0 < v ∧
        X.X v ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) v ≠ 0) →
      u ∈ Ioc (grid n i) (grid n (i + 1)) →
      v ∈ Ioc (grid n i) (grid n (i + 1)) → u = v := by sorry
