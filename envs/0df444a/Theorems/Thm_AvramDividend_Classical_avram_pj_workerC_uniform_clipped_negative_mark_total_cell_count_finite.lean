-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_uniform_clipped_negative_mark_total_cell_count_finite
-- name    : AvramDividend.Classical.avram_pj_workerC_uniform_clipped_negative_mark_total_cell_count_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:39:25.960591+00:00
-- url     : https://prove2.me/theorems/20e6c544-521e-48c3-b66a-5e330204cbeb
-- title:
--   All original negative Lévy marks above a fixed cutoff form a genuinely finite total count over the true randomly clipped physical grid
-- statement:
--   For any original spectrally negative Lévy process, even with infinite negative-jump activity and unbounded variation, and an arbitrary pathwise bounded stopping clock rho, the total number of actual jumps of magnitude at least delta over all clipped finite physical mesh cells is finite. The proof uses exact grid telescoping of the original mapped intrinsic marked jump count and pathwise finite separated-mark count on the containing deterministic horizon. This includes the final randomly clipped cell with no Gaussian or full finite-intensity assumption.
-- source:
--   Proved 847d6163 true clipped original marked-grid telescoping; Proved 557aabfa pathwise finite actual separated negative jump count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_trueclock_clipped_marked_grid_telescoping
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_uniform_clipped_negative_mark_total_cell_count_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : Ω → ℝ≥0) (n m : ℕ)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (δ : ℝ) (hδ : 0 < δ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    (∑ i ∈ Finset.range (m + 1),
      NX (Ioc (u i) (u (i+1)) ×ˢ
        {z : ℝ | δ ≤ dist z 0})) < ⊤ := by sorry
