-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_occupied_grid_count_measurable_20261116
-- name    : AvramDividend.Classical.avram_a26_original_physical_occupied_grid_count_measurable_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:23:50.731359+00:00
-- url     : https://prove2.me/theorems/66a25905-20bb-4259-a756-96b4cc7aa379
-- title:
--   Original physical negative-Borel occupied equal-grid count is measurable
-- statement:
--   Each original-space marked Borel cell count on (iT/n,(i+1)T/n] is measurable by the Proved original physical rectangle count measurability theorem 8146a449. Its nonzero indicator is measurable, hence the finite sum of occupied-cell indicators and the corresponding filtered finite-set cardinal are measurable on unchanged Omega. This is needed to use the generic binomial count coupling convergence theorem.
-- source:
--   Proved original physical rectangle count measurability 8146a449 and finite measurable indicator sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_original_physical_occupied_grid_count_measurable_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) :
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
    ∀ n : ℕ, Measurable (Z n) := by sorry
