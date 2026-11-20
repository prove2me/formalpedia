-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_rightmesh_eventually_below_strict_horizon
-- name    : AvramDividend.Classical.avram_f6_original_rightmesh_eventually_below_strict_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:05:30.781361+00:00
-- url     : https://prove2.me/theorems/89bfcf79-5bfc-441a-908a-b8c81c7cf6a1
-- title:
--   Original delayed physical stopping clock eventually stays below a strictly later horizon
-- statement:
--   When original subclock sigma is strictly before bounded stopping horizon tau, its physical right-shifted approximants min(tau,sigma+1/(m+1)) are eventually strictly before tau; enables correct pre-ruin vs ruin-contact branch at the true original clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_delayed_clock_real_min_tends_to_stopped
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_rightmesh_eventually_below_strict_horizon
    (σ τ : ℝ≥0) (hστ : σ < τ) :
    ∀ᶠ m : ℕ in atTop,
      min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1)) < τ := by sorry
