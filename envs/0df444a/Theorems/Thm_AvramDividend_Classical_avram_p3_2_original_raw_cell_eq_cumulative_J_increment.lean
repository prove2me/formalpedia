-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_raw_cell_eq_cumulative_J_increment
-- name    : AvramDividend.Classical.avram_p3_2_original_raw_cell_eq_cumulative_J_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:04:29.154735+00:00
-- url     : https://prove2.me/theorems/7f6c3677-66eb-429e-a4ce-b1831507af95
-- title:
--   Physical original raw negative-jump half-open cell equals actual cumulative J endpoint increment
-- statement:
--   For the original BV spectrally negative Lévy process, on one full-measure event and simultaneously for every monotone finite physical stopping grid, the genuine raw negative-jump tsum over each half-open cell (u_i,u_{i+1}] is exactly the increment of the original cumulative jump path J. This is the source-exact interface between the P3-2 cap-linear drift/jump commutator and F2's mesh commutator expressed in J endpoint increments.
-- source:
--   Direct application of the independently Proved original raw cumulative disjoint interval additivity 50ef916b; no process replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_raw_cell_eq_cumulative_J_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      (∀ i : ℕ, i < n → u i ≤ u (i + 1)) →
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      ∀ i : ℕ, i < n →
        (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = J (u (i + 1)) - J (u i) := by sorry
