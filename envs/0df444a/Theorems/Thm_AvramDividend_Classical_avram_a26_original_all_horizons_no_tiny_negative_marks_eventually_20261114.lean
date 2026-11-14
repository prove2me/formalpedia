-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_all_horizons_no_tiny_negative_marks_eventually_20261114
-- name    : AvramDividend.Classical.avram_a26_original_all_horizons_no_tiny_negative_marks_eventually_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:37:20.294203+00:00
-- url     : https://prove2.me/theorems/2b889ad5-f38f-4341-b7cb-f9d6b4d3e4d0
-- title:
--   One original source conull event with eventually no actual jumps in shrinking omitted negative-mark bands on every horizon
-- statement:
--   On one common conull event for the original finite-activity spectrally negative Levy process, every finite time horizon eventually contains no physical negative jumps in the omitted shrinking band for every sufficiently large cutoff.
-- source:
--   A26 common conull physical negative-mark margin and pinned tendsto_one_div_add_atTop_nhds_zero_nat.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original finite-activity shrinking omitted negative mark bands are eventually empty on every horizon on one common source event. -/

theorem AvramDividend.Classical.avram_a26_original_all_horizons_no_tiny_negative_marks_eventually_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ∃ N : ℕ, ∀ n ≥ N, ∀ u : ℝ≥0, 0 < u → u ≤ T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
          ∉ Ioo (-(1 / ((n : ℝ) + 1))) 0 := by sorry
