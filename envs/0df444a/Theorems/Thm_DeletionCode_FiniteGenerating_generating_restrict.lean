-- Prove2me | Theorems.Thm_DeletionCode_FiniteGenerating_generating_restrict
-- name    : DeletionCode.FiniteGenerating.generating_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:28.340183+00:00
-- url     : https://prove2.me/theorems/be9824e4-51fe-4849-8697-f5010c0452dc
-- title:
--   Finite Generating: generating restrict
-- statement:
--   The Finite Generating construction uses the generating restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L38-L49
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L38-L49

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
import Theorems.Thm_DeletionCode_GeneratingBlocks_generating_restrict

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition

theorem DeletionCode.FiniteGenerating.generating_restrict {k : ℕ} (v : Gram (windowLength k) → ℤ)
    (G U : RuleSet k) (rank : (Gram (windowLength k) → ℤ) → ℕ)
    (hUG : U ⊆ G) (hclosed : ClosedIn G U) (hgen : GeneratingOn v G rank) :
    GeneratingOn v U rank := by sorry
