-- Prove2me | Theorems.Thm_DeletionCode_ManuscriptCounting_generatingSet_finite
-- name    : DeletionCode.ManuscriptCounting.generatingSet_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:22:59.530781+00:00
-- url     : https://prove2.me/theorems/85fc4a6b-0921-4b42-80ce-e0792e09e1bc
-- title:
--   Manuscript Counting: generating Set finite
-- statement:
--   The Manuscript Counting construction uses the generating Set finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ManuscriptCounting.lean#L49-L56
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ManuscriptCounting.lean#L49-L56

import Definitions.Def_DeletionCode_CountingLemma
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_ManuscriptCounting
import Theorems.Thm_DeletionCode_CountingLemma_generatingSet_finite

set_option autoImplicit true
open DeletionCode DeletionCode.ManuscriptCounting
open Windows HeaderRecovery CatalogueWords CatalogueBridge SignedSupport
open RuleReconstruction RuleSetGraph SignedRuleCount CountExponent CanonicalIndex

theorem DeletionCode.ManuscriptCounting.generatingSet_finite (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) :
    Finite {Q : RuleSet k // GeneratingSet t x n k R c Q} := by sorry
