-- Prove2me | Theorems.Thm_DeletionCode_CountingLemma_generatingSet_record_bound
-- name    : DeletionCode.CountingLemma.generatingSet_record_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:28.510723+00:00
-- url     : https://prove2.me/theorems/29bc3a27-64ca-4a04-a093-df4c3d9371f0
-- title:
--   Counting Lemma: generating Set record bound
-- statement:
--   The Counting Lemma construction uses the generating Set record bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CountingLemma.lean#L50-L58
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CountingLemma.lean#L50-L58

import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_CountingLemma
set_option autoImplicit true
open DeletionCode DeletionCode.CountingLemma
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RuleSetGraph SignedRuleCount DescriptionCount CountExponent

theorem DeletionCode.CountingLemma.generatingSet_record_bound (x : Letters) (n k ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // GeneratingSet x n k ν R c group Q} ≤
      n ^ c * fieldBound (windowLength k) ν ^ (50 * ν) := by sorry
