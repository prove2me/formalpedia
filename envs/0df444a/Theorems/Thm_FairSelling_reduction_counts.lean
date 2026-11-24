-- Prove2me | Theorems.Thm_FairSelling_reduction_counts
-- name    : FairSelling.reduction_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:15:19.353222+00:00
-- url     : https://prove2.me/theorems/465bf594-e970-43ac-9f6f-28dc43997ba3
-- title:
--   Fair Selling: reduction counts
-- statement:
--   The counting of the pairing step: `t = |L₀| − n₀ − 1` pure bundles can be created out of the
--   large goods, and afterwards there is exactly one more large good than bundles still to create.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsReduction.lean#L28-L31
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsReduction.lean#L28-L31

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsReduction
set_option autoImplicit true
open FairSelling

theorem FairSelling.reduction_counts {L n0 n2 : ℕ} (hlow : n0 + 1 < L) (hhigh : L < 2 * n0)
    (hcard : L ≤ n0 + n2 + 1) :
    (L - n0 - 1 ≤ n2) ∧ L - 2 * (L - n0 - 1) = (n0 - (L - n0 - 1)) + 1 := by sorry
