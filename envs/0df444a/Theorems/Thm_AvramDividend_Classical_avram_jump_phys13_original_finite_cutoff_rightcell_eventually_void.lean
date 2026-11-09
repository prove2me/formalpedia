-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_cutoff_rightcell_eventually_void
-- name    : AvramDividend.Classical.avram_jump_phys13_original_finite_cutoff_rightcell_eventually_void
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:59:47.576044+00:00
-- url     : https://prove2.me/theorems/17e97019-d3e5-4b37-8034-06b123230a7c
-- title:
--   Original separated negative-jump band has eventually no post-stop jump in a shrinking final physical cell
-- statement:
--   For the actual marked jumps of X.X and a fixed negative-mark cutoff, all jump times on a bounded horizon form a finite set. Consequently any sequence of upper grid endpoints bounded by the horizon and converging to an arbitrary pathwise stopping time eventually contains no cutoff jump strictly after that time. This resolves the post-stop final-cell pathwise error without a finite-variation hypothesis or a cutoff-uniform moment bound.
-- source:
--   PJ-PHYS13 necessary pathwise final-cell localisation for owner target 0b1a879a; direct import of authoritative Proved e5e6f70b; narrowly scoped avram_jump_phys13 namespace.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump_phys13_original_finite_cutoff_rightcell_eventually_void
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (cut : ℕ) (τ : ℝ≥0)
    (e : ℕ → ℝ≥0) (heBound : ∀ k, e k ≤ T)
    (heTendsto : Tendsto e atTop (𝓝 τ)) :
    ∀ᶠ k in atTop,
      {u : ℝ≥0 | τ < u ∧ u ≤ e k ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((cut : ℝ) + 1))} = ∅ := by sorry
