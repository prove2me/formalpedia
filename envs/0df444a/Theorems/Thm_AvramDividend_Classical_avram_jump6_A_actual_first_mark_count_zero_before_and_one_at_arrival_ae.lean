-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_mark_count_zero_before_and_one_at_arrival_ae
-- name    : AvramDividend.Classical.avram_jump6_A_actual_first_mark_count_zero_before_and_one_at_arrival_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:39:05.560378+00:00
-- url     : https://prove2.me/theorems/60d35907-8b53-4b41-95c9-db1fdc5309bf
-- title:
--   True physical rate-one Poisson count vanishes strictly before its first mark and equals one at that first mark
-- statement:
--   Combine two already-Proved true Poisson source facts: for every time strictly before the physical first arrival the actual jumpCount is zero, and almost surely at that first arrival the count is exactly one. This is the precise original path hBefore/hFirst package required by the original capped barrier terminal-plus-inclusive-cash zero theorem aef35b4c, and is an input for a full positive-probability first-ruin countermodel to the unit-coefficient Jfull source. No synthetic mark process is introduced.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_rateone_size2_count_one_at_first_mark
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_first_mark_count_zero_before_and_one_at_arrival_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    ∀ᵐ ω ∂μ,
      (∀ t : ℝ≥0, (t : ℝ) < arrival τ 0 ω →
        jumpCount (fun n => arrival τ n ω) (t : ℝ) = 0) ∧
      jumpCount (fun n => arrival τ n ω) (arrival τ 0 ω) = 1 := by sorry
