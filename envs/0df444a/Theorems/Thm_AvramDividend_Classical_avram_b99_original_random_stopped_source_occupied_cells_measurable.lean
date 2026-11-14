-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b99_original_random_stopped_source_occupied_cells_measurable
-- name    : AvramDividend.Classical.avram_b99_original_random_stopped_source_occupied_cells_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:47:42.781061+00:00
-- url     : https://prove2.me/theorems/129d33e3-0507-4a71-93cf-0cf00d386d16
-- title:
--   Exact original random stopping-grid occupied finite negative-band source cell count is measurable
-- statement:
--   For every finite grid S and genuine sample-path-dependent, measurable original source clocks s_i,t_i, count cells whose interval has nonzero actual original negative-jump Poisson source mark count in the Lévy size band. Proved original random interval count measurability applies to each of the random clock pairs, making its positive-count event measurable. A finite sum of their indicators in ENNReal is measurable. This replaces the deterministic grid hypothesis of B96 and makes the marked source occupancy at true stopped random endpoints measurable for finite negative bands. Removing the cutoff and bounding all-negative count is a separate step.
-- source:
--   Proved avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable, genuine original Lévy marked point count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original negative-band occupied-cell count is measurable for genuine random source grid clocks. -/

theorem AvramDividend.Classical.avram_b99_original_random_stopped_source_occupied_cells_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (cut : ℕ) (S : Finset ℕ)
    (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i ∈ S, Measurable (s i))
    (ht : ∀ i ∈ S, Measurable (t i)) :
    Measurable (fun ω : Ω =>
      ∑ i ∈ S,
        if ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc (s i ω) (t i ω) ×ˢ
              Iic (-(1 / ((cut : ℝ) + 1)))) ≠ 0 then
          (1 : ℝ≥0∞) else 0) := by sorry
