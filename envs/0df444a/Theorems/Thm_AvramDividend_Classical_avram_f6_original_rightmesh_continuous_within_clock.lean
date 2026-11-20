-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_rightmesh_continuous_within_clock
-- name    : AvramDividend.Classical.avram_f6_original_rightmesh_continuous_within_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:55:00.542043+00:00
-- url     : https://prove2.me/theorems/f2c24367-76b7-4038-b7bb-322c4ada26da
-- title:
--   Original right-delayed compact clock transfers right continuity to pathwise values
-- statement:
--   For σ≤τ, all real-valued paths right-continuous at σ converge at min(τ,σ+1/(m+1)) to their value at σ, in the genuine NNReal physical clock. This is the deterministic transfer lemma for the original postpayment reserve and ruin-contact source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_delayed_clock_real_min_tends_to_stopped
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_rightmesh_continuous_within_clock
    (σ τ : ℝ≥0) (hστ : σ ≤ τ)
    (f : ℝ≥0 → ℝ)
    (hf : ContinuousWithinAt f (Ici σ) σ) :
    Tendsto (fun m : ℕ =>
      f (min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))))
      atTop (𝓝 (f σ)) := by sorry
