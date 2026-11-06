-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_rightcont_terminal_adapted_prefix
-- name    : AvramDividend.Classical.avram_p4_s3_run1640_rightcont_terminal_adapted_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:53:13.828124+00:00
-- url     : https://prove2.me/theorems/1fc1a353-5b42-4439-9ebc-40bd9c1f5eab
-- title:
--   Completed adapted physical martingale increments imply every right-continuous predictable grid prefix
-- statement:
--   On any monotone deterministic grid and original right-continuous filtration, if each compensated physical increment is measurable at the following grid time, every finite past sum is measurably adapted at its present grid time. Discharges hPrefix in the Proved original physical right-continuous L2 isometry without any stochastic independence or added axioms.
-- source:
--   Mathlib monotone_nat_of_le_succ, Filtration.rightCont monotonicity and Finset.stronglyMeasurable_sum, all at pinned revision. Works for original physical D and never assumes prefix adaptedness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1640_rightcont_terminal_adapted_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (D : ℕ → Ω → ℝ)
    (hTerminal : ∀ j,
      StronglyMeasurable[𝓕.rightCont (grid (j + 1))] (D j)) :
    ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω) := by sorry
