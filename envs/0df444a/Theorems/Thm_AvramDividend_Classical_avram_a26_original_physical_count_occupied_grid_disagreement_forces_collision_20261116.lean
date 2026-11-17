-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_count_occupied_grid_disagreement_forces_collision_20261116
-- name    : AvramDividend.Classical.avram_a26_original_physical_count_occupied_grid_disagreement_forces_collision_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:59:20.339898+00:00
-- url     : https://prove2.me/theorems/c43974e9-7289-48d6-bbc9-f82e34371eb6
-- title:
--   Original physical marked-count and occupied-grid count can disagree only through a multiple-jump cell
-- statement:
--   On the original probability space, finite negative Lévy activity implies the marked-jump time set is almost surely finite. Partition (0,T] into n positive equal cells. With no multiple B-marked jump in any cell, the original total count agrees with the number of occupied cells. Therefore any disagreement forces a cell with at least two jumps. Use the proved physical finite marked-time count theorem 8f1dd77e and source a.e. finite support c6cc76c9; this is the pathwise heart of the grid coupling.
-- source:
--   Proved source physical marked finite support c6cc76c9 and interval count finite marked time cardinal identity 8f1dd77e; finite partition combinatorics.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_original_physical_count_occupied_grid_disagreement_forces_collision_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
    let Z : ℕ → Ω → ℕ := fun n ω =>
      ((Finset.range n).filter (fun i : ℕ =>
        NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0)).card
    ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n →
      K ω ≠ Z n ω →
      ∃ i ∈ Finset.range n,
        (2 : ℝ) ≤
          (NX ω (Ioc ((i : ℝ≥0) * δ n)
            (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B)).toReal := by sorry
