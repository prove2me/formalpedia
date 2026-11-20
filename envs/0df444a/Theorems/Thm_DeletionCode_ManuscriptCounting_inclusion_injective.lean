-- Prove2me | Theorems.Thm_DeletionCode_ManuscriptCounting_inclusion_injective
-- name    : DeletionCode.ManuscriptCounting.inclusion_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:55.01004+00:00
-- url     : https://prove2.me/theorems/f7a76e48-381b-4cb7-b2b4-fb72a3bd8c90
-- title:
--   Manuscript Counting: inclusion injective
-- statement:
--   The Manuscript Counting construction uses the inclusion injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ManuscriptCounting.lean#L42-L47
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ManuscriptCounting.lean#L42-L47

import Definitions.Def_DeletionCode_CountingLemma
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_ManuscriptCounting
set_option autoImplicit true
open DeletionCode DeletionCode.ManuscriptCounting
open Windows HeaderRecovery CatalogueWords CatalogueBridge SignedSupport
open RuleReconstruction RuleSetGraph SignedRuleCount CountExponent CanonicalIndex

theorem DeletionCode.ManuscriptCounting.inclusion_injective (t : ℕ) (x : Letters) (n k R c : ℕ) :
    Function.Injective (inclusion t x n k R c) := by sorry
