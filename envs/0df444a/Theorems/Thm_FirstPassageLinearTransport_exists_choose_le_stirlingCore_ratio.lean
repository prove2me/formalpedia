-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_choose_le_stirlingCore_ratio
-- name    : FirstPassageLinearTransport.exists_choose_le_stirlingCore_ratio
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:20:52.11681+00:00
-- url     : https://prove2.me/theorems/c6cd4fe8-0ef5-51cb-9491-b85d2012f8cc
-- title:
--   First Passage Linear Transport: exists choose le stirling Core ratio
-- statement:
--   A uniform Stirling bound for every nontrivial binomial coefficient.  The
--   remaining ratio of `stirlingCore`s is converted to entropy in the next layer.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L415-L465
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L415-L465

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

theorem FirstPassageLinearTransport.exists_choose_le_stirlingCore_ratio :
    ∃ C : ℝ, 0 < C ∧
      ∀ r k : ℕ, 0 < k → k < r →
        (r.choose k : ℝ) ≤
          C * stirlingCore r /
            (stirlingCore k * stirlingCore (r - k)) := by sorry
