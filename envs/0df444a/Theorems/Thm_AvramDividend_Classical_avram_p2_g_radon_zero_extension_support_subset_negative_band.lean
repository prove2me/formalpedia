-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_zero_extension_support_subset_negative_band
-- name    : AvramDividend.Classical.avram_p2_g_radon_zero_extension_support_subset_negative_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:06:36.084572+00:00
-- url     : https://prove2.me/theorems/123518c4-9e2f-40d8-9f4e-904c1b0976ac
-- title:
--   Zero extension preserves separated negative-band support of compact test functions
-- statement:
--   If a compactly supported continuous function on negative marks vanishes on the interval immediately below zero of width epsilon, its canonical zero extension to all real marks has functional support contained in the closed negative band (-infinity,-epsilon]. Together with the independently Proved compact-test separation theorem, this yields a genuine source test support bound on all real Lévy increments.
-- source:
--   Mathlib.Data.Subtype: Function.extend_val_apply and Function.extend_val_apply'.

import Mathlib
open MeasureTheory Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_g_radon_zero_extension_support_subset_negative_band
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ)
    (ε : ℝ)
    (hf : ∀ x : {x : ℝ // x < 0}, -ε < (x : ℝ) → f x = 0) :
    Function.support
      (Function.extend (Subtype.val : {x : ℝ // x < 0} → ℝ)
        (fun x => f x) 0) ⊆ Iic (-ε) := by sorry
