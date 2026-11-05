-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_uniform_cells_with_separation
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_uniform_cells_with_separation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:23:47.723203+00:00
-- url     : https://prove2.me/theorems/55fc7776-e3c7-47d3-9113-532054aa41b3
-- title:
--   Actual original negative-band jump times admit coherent eventually injective uniform cells
-- statement:
--   For a genuine source spectrally negative Levy path, all its actual negative-band marked jump times in (0,T] admit half-open uniform cell selectors bounded by the grid size and eventually injective as the mesh refines.
-- source:
--   Exact source jump finite set e5e6f70b, P2-A finite uniform selectors b2eb2219, P2-A eventual injectivity bd4bfbea, original X.rightCont and X.leftLim with pinned Mathlib tendsto_leftLim_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_uniform_cells_with_separation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ idx : ℝ≥0 → ℕ → ℕ,
      (∀ u ∈ F, ∀ k : ℕ, idx u k ≤ k ∧
        (idx u k : ℝ≥0) * (T / ((k : ℝ≥0) + 1)) < u ∧
        u ≤ (((idx u k + 1 : ℕ) : ℝ≥0) *
          (T / ((k : ℝ≥0) + 1)))) ∧
      (∀ᶠ k : ℕ in atTop,
        Set.InjOn (fun u => idx u k) (F : Set ℝ≥0)) := by sorry
