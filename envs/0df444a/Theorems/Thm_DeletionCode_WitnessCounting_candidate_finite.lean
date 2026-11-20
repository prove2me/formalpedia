-- Prove2me | Theorems.Thm_DeletionCode_WitnessCounting_candidate_finite
-- name    : DeletionCode.WitnessCounting.candidate_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:30:28.502038+00:00
-- url     : https://prove2.me/theorems/ae1ef3aa-f396-4bc5-86b4-56b5fb378af3
-- title:
--   Witness Counting: candidate finite
-- statement:
--   The Witness Counting construction uses the candidate finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean#L86-L94
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean#L86-L94

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

theorem DeletionCode.WitnessCounting.candidate_finite (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) :
    Finite {U : RuleSet k // Candidate t x n k R U} := by sorry
