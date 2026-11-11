-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys44_original_cap_reward_bounded_below_cap
-- name    : AvramDividend.Classical.avram_bvb_phys44_original_cap_reward_bounded_below_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:48:52.096266+00:00
-- url     : https://prove2.me/theorems/df040a51-55df-40ae-bd16-d3b8655edaf8
-- title:
--   Continuous nonnegative-reserve reward is uniformly bounded below a finite cap
-- statement:
--   A function continuous on nonnegative reserves and identically zero below zero has a uniform absolute bound on all reserve values below any fixed nonnegative finite cap. This is the finite-activity original jump-kernel envelope used in the physical BV compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys44_original_cap_reward_bounded_below_cap
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : ℝ, y ≤ c → |w y| ≤ R := by sorry
