-- Prove2me | Theorems.Thm_DeletionCode_CountingLemma_generatingSet_finite
-- name    : DeletionCode.CountingLemma.generatingSet_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:15.702562+00:00
-- url     : https://prove2.me/theorems/518530aa-8236-4df5-ab1d-de886480729b
-- title:
--   Counting Lemma: generating Set finite
-- statement:
--   The Counting Lemma construction uses the generating Set finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CountingLemma.lean#L42-L48
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CountingLemma.lean#L42-L48

import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_CountingLemma
set_option autoImplicit true
open DeletionCode DeletionCode.CountingLemma
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RuleSetGraph SignedRuleCount DescriptionCount CountExponent

theorem DeletionCode.CountingLemma.generatingSet_finite (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {Q : RuleSet k // GeneratingSet x n k ν R c group Q} := by sorry
