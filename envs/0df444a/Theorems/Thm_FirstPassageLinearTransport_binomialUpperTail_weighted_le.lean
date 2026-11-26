-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_binomialUpperTail_weighted_le
-- name    : FirstPassageLinearTransport.binomialUpperTail_weighted_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:27.212352+00:00
-- url     : https://prove2.me/theorems/c7e7efdf-bef1-4976-8bad-ae6c1773a12f
-- title:
--   First Passage Linear Transport: binomial Upper Tail weighted le
-- statement:
--   A binomial upper tail above the midpoint is controlled by its first
--   coefficient.  The proof is an exact telescoping argument: the factor
--   `2 * k - r` is the distance from the midpoint.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L137-L173
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L137-L173

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

theorem FirstPassageLinearTransport.binomialUpperTail_weighted_le
    {r k : ℕ} (hkr : k ≤ r) (hhalf : r < 2 * k) :
    (((2 * k : ℕ) : ℝ) - (r : ℝ)) * (binomialUpperTail r k : ℝ) ≤
      (k : ℝ) * (r.choose k : ℝ) := by sorry
