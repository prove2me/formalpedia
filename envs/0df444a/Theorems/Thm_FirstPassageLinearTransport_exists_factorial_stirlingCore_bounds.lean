-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_factorial_stirlingCore_bounds
-- name    : FirstPassageLinearTransport.exists_factorial_stirlingCore_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:57.28439+00:00
-- url     : https://prove2.me/theorems/54534b09-78b1-413e-91ac-fac8f0bd0921
-- title:
--   First Passage Linear Transport: exists factorial stirling Core bounds
-- statement:
--   Uniform two-sided factorial bounds obtained from monotonicity and the
--   positive lower bound of Mathlib's Stirling sequence.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L392-L411
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L392-L411

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_factorial_stirlingCore_bounds :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ n : ℕ, 0 < n →
        a * stirlingCore n ≤ (Nat.factorial n : ℝ) ∧
          (Nat.factorial n : ℝ) ≤ b * stirlingCore n := by sorry
