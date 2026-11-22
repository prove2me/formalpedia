-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_terminal_zero_prestate_fixed_negative_mark_raw_value_limit
-- name    : AvramDividend.Classical.avram_freshD_original_terminal_zero_prestate_fixed_negative_mark_raw_value_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T09:08:31.647637+00:00
-- url     : https://prove2.me/theorems/c8a0019e-9733-4163-80cd-1f1ed8a77497
-- title:
--   Actual fixed negative Lévy mark from zero terminal pre-reserve has raw value increment tending to minus w(0)
-- statement:
--   For a genuine fixed negative Lévy jump mark z<0 and original candidate value w continuous on nonnegative reserves and identically zero below zero, if physical grid sampled pre-jump reserves u_m approach zero while remaining nonnegative eventually, then the RAW nonlinear value increment w(u_m+z)-w(u_m) converges to -w(0). The negative-mark poststate is eventually strictly negative, hence its value is exactly zero, while the prestate value converges to w(0) from the nonnegative side. This handles the exceptional terminal ruin-causing negative mark with zero predictable pre-reserve, preserving w(0)>0. It does not make the false claim that the compensated Taylor derivative term converges at zero, which may require separate boundary analysis.
-- source:
--   Original Avram Dividend physical stopped finite-activity marked Itô–Meyer terminal ruin cell 242ca5f1, genuine negative mark and zero value extension to negative reserve.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_terminal_zero_prestate_fixed_negative_mark_raw_value_limit
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (z : ℝ) (hz : z < 0)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 (0 : ℝ)))
    (hpos : ∀ᶠ m in atTop, 0 ≤ u m) :
    Tendsto (fun m => w (u m + z) - w (u m))
      atTop (𝓝 (-w 0)) := by sorry
