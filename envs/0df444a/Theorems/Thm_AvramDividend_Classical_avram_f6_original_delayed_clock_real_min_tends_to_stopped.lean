-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_delayed_clock_real_min_tends_to_stopped
-- name    : AvramDividend.Classical.avram_f6_original_delayed_clock_real_min_tends_to_stopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:29:34.922918+00:00
-- url     : https://prove2.me/theorems/5a2426a5-a1d8-423d-bacf-235276ee9c5e
-- title:
--   True original delayed compact clock converges back to stopped clock in real time
-- statement:
--   For any original subordinate stopping time realised by nonnegative real σ bounded by a ruin-clipped horizon τ, the physical one-sided clock min(τ,σ+1/(m+1)) in real coordinates converges to σ. This is the precise physical deterministic clock-convergence input to the original stopped Ito/HJB ruin-contact/Fatou source, with no invented random process or stochastic witness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_delayed_clock_real_min_tends_to_stopped
    (σ τ : ℝ≥0) (hστ : σ ≤ τ) :
    Tendsto (fun m : ℕ =>
      min (τ : ℝ) ((σ : ℝ) + (1 : ℝ) / ((m : ℝ) + 1)))
      atTop (𝓝 (σ : ℝ)) := by sorry
