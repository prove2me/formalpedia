-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise39_original_dyadic_mark_partition_count_rate_bound
-- name    : AvramDividend.Classical.avram_anoise39_original_dyadic_mark_partition_count_rate_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:50:32.698131+00:00
-- url     : https://prove2.me/theorems/c4fb2de1-bbc1-4b83-9077-ac1ba772db25
-- title:
--   Original dyadic disjoint physical count and intensity budget
-- statement:
--   For the original marked-jump measure, each finite dyadic negative-mark partition is disjoint. Its total physical count over (s,t] is at most the original all-negative count through t. The corresponding sum of Levy intensities is at most the all-negative Levy mass. Both inequalities are pathwise and remain valid before any moment assumptions.
-- source:
--   Single necessary finite mark-partition count and intensity certificate for root-connected Open anoise38 ed61f8be. Reuses published original finite disjoint Borel mark partition theorem 33203d98.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise39_original_dyadic_mark_partition_count_rate_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ n k : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → Set ℝ := fun i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → Ω → ℝ≥0∞ := fun i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C i)
      let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ Iio (0 : ℝ))
      (∀ ω, (∑ i ∈ Finset.range (2 ^ k), J i ω) ≤ N ω) ∧
        (∑ i ∈ Finset.range (2 ^ k), X.ν (C i)) ≤ X.ν (Iio (0 : ℝ)) := by sorry
