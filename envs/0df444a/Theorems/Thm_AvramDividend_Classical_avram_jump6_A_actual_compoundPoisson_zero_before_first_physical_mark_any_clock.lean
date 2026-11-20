-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_compoundPoisson_zero_before_first_physical_mark_any_clock
-- name    : AvramDividend.Classical.avram_jump6_A_actual_compoundPoisson_zero_before_first_physical_mark_any_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:51:48.213176+00:00
-- url     : https://prove2.me/theorems/17227efd-426c-419e-9846-76e09a778cd5
-- title:
--   Original compound Poisson physical path vanishes before its actual first arrival at any real time
-- statement:
--   For any original marked compound Poisson driver and physical path, whenever a real clock t occurs strictly before the first arrival τ0, jumpCount at t is exactly zero and therefore compoundPoisson(0,τ,Y)_t=0. No rate assumption, no mark law and no almost-sure exceptions are needed. Together with the native Brownian small tube, this yields positive controlled reserves until the first negative size-two mark, hence ruinTime ≥ the physical first arrival.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Finset
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_compoundPoisson_zero_before_first_physical_mark_any_clock
    {Ω : Type*} [MeasurableSpace Ω]
    (τ Y : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω)
    (ht : t < arrival τ 0 ω) :
    compoundPoisson (0 : ℝ) τ Y t ω = 0 := by sorry
