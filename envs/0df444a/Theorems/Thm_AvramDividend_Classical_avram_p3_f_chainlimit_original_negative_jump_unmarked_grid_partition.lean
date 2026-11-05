-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:16:25.680309+00:00
-- url     : https://prove2.me/theorems/df3481a1-c504-4fe5-a595-1beb56c68125
-- title:
--   Exact original negative-jump source grid partition into marked and unmarked cells
-- statement:
--   For the exact raw negative-left-jump sum J of the original bounded-variation spectrally negative Lévy process, every finite true-time grid partitions the cumulative source jump increment into cells carrying finitely marked indices and their complement. This is a pathwise identity on the original X.X and (0,t] left-jump chronology, with no replacement source or stochastic compensation. The remaining atom-position task must show marked cells capture selected significant original jump times, making the unmarked side a small source tail.
-- source:
--   Actual X.X original negative-left-jump Stieltjes source J, telescope of adjacent (u_i,u_(i+1)] increments, marked/unmarked index partition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ) (S : Finset ℕ) :
    ∀ ω,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω
        else 0
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      (∑ i ∈ Finset.range n, if i ∈ S then 0 else j i) +
        (∑ i ∈ Finset.range n, if i ∈ S then j i else 0) =
      J (u n) - J (u 0) := by sorry
