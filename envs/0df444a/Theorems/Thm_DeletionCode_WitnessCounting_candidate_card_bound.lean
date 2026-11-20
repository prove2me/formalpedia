-- Prove2me | Theorems.Thm_DeletionCode_WitnessCounting_candidate_card_bound
-- name    : DeletionCode.WitnessCounting.candidate_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:30:30.731172+00:00
-- url     : https://prove2.me/theorems/6d48540d-3be2-45a2-900f-4b50dda6d4ae
-- title:
--   Witness Counting: candidate card bound
-- statement:
--   The fixed-size witness-set count used before the random-hash union bound.
--   No ordering, catalogue presentation, or occurrence multiplicity is counted.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean#L115-L148
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean#L115-L148

import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_WitnessCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_WitnessCounting
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCounting
open Windows HeaderRecovery SignedRuleCount RuleSetGraph CountExponent
open ManuscriptCounting WitnessCases FiniteGenerating
open scoped BigOperators

theorem DeletionCode.WitnessCounting.candidate_card_bound (t : ℕ) (ht : 2 ≤ t) (x : Letters)
    (n k R : ℕ) (hR : 2 ≤ R) (hx : KUnique x n k) (hn : 1 ≤ n)
    (hbonus : windowLength k < R → n ≤ 2 ^ R) :
    Nat.card {U : RuleSet k // Candidate t x n k R U} ≤
      2 ^ R * (2 * t * R + 1) * n ^ ((2 * t - 1) * R) *
        (windowLength k * R) ^ (exponent t * R) := by sorry
