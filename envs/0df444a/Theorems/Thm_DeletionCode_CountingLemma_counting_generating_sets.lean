-- Prove2me | Theorems.Thm_DeletionCode_CountingLemma_counting_generating_sets
-- name    : DeletionCode.CountingLemma.counting_generating_sets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:11.588763+00:00
-- url     : https://prove2.me/theorems/e15431ab-cbc2-4067-ba2e-b57993eea2cf
-- title:
--   Counting Lemma: counting generating sets
-- statement:
--   The counting lemma's explicit bound for ν=2tR bubble occurrences.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CountingLemma.lean#L61-L68
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CountingLemma.lean#L61-L68

import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_CountingLemma
set_option autoImplicit true
open DeletionCode DeletionCode.CountingLemma
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RuleSetGraph SignedRuleCount DescriptionCount CountExponent

theorem DeletionCode.CountingLemma.counting_generating_sets (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k)
    (group : Fin (2 * t * R) → Fin R) :
    Nat.card {Q : RuleSet k // GeneratingSet x n k (2 * t * R) R c group Q} ≤
      n ^ c * (windowLength k * R) ^ (exponent t * R) := by sorry
