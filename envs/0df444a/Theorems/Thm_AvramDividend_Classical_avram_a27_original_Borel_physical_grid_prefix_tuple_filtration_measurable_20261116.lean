-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_Borel_physical_grid_prefix_tuple_filtration_measurable_20261116
-- name    : AvramDividend.Classical.avram_a27_original_Borel_physical_grid_prefix_tuple_filtration_measurable_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:39:10.642368+00:00
-- url     : https://prove2.me/theorems/7be7142d-96ed-4753-8f0e-37b0722eb1bd
-- title:
--   Original physical marked Borel count tuple over any finite grid prefix is measurable at its original filtration endpoint
-- statement:
--   For the actual original Lévy process, each finite tuple of B-marked physical cell counts in the first k cells of the n-grid is jointly measurable with respect to the original filtration at time k*T/n. This follows from original cadlag path adaptedness, physical jump extraction from the stopped path and the Proved original Borel prefix count filtration measurability b25029d5. It is the exact source measurability premise needed to apply Proved independence of any past observable from a future physical marked count. No independent companion process.
-- source:
--   Proved original Borel past count filtration measurability b25029d5; original process adapted cadlag path extraction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_Borel_physical_grid_prefix_tuple_filtration_measurable_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℝ≥0 := T / (n : ℝ≥0)
    ∀ k : ℕ, k ≤ n →
      Measurable[𝓕 ((k : ℝ≥0) * δ)] (fun ω : Ω =>
        fun i : Fin k => NX ω (Ioc ((i.val : ℝ≥0) * δ)
          (((i.val + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B)) := by sorry
