-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_occupied_Borel_grid_indicator_zero_one_and_card_sum_20261116
-- name    : AvramDividend.Classical.avram_a27_original_occupied_Borel_grid_indicator_zero_one_and_card_sum_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:32:13.273495+00:00
-- url     : https://prove2.me/theorems/a6e6ed38-f7bd-41e7-b65d-cace17516c62
-- title:
--   Original physical occupied Borel grid indicators are zero-one and their sum equals the occupied-cell count
-- statement:
--   For any actual original spectrally negative Lévy physical marked jump measure, the equal-grid physical occupied-cell indicators are pathwise zero or one and their sum over Fin n equals exactly the number of physically occupied grid cells. This is deterministic and follows from Proved finite-range filtered-cardinality equals sum-of-indicators 441b76b7. It isolates the source physical indicator representation for exact binomial law without any stochastic independence assumptions.
-- source:
--   Proved Finset filtered cardinal vs Fin Bernoulli indicator sum 441b76b7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_occupied_Borel_grid_indicator_zero_one_and_card_sum_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (n : ℕ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℝ≥0 := T / (n : ℝ≥0)
    let Y : Fin n → Ω → ℕ := fun i ω =>
      if NX ω (Ioc ((i.val : ℝ≥0) * δ)
        (((i.val + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B) = 0
      then 0 else 1
    let Z : Ω → ℕ := fun ω =>
      ((Finset.range n).filter (fun i : ℕ =>
        NX ω (Ioc ((i : ℝ≥0) * δ)
          (((i + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B) ≠ 0)).card
    (∀ i ω, Y i ω = 0 ∨ Y i ω = 1) ∧
      (∀ ω, Z ω = ∑ i : Fin n, Y i ω) := by sorry
