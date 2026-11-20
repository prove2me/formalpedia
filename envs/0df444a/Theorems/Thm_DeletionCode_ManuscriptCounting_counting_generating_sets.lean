-- Prove2me | Theorems.Thm_DeletionCode_ManuscriptCounting_counting_generating_sets
-- name    : DeletionCode.ManuscriptCounting.counting_generating_sets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:46.825888+00:00
-- url     : https://prove2.me/theorems/f4196fe0-d271-4a65-825f-a8d574696c0c
-- title:
--   Manuscript Counting: counting generating sets
-- statement:
--   The existence-of-a-constant formulation of the manuscript's counting lemma.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ManuscriptCounting.lean#L87-L93
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ManuscriptCounting.lean#L87-L93

import Definitions.Def_DeletionCode_CountingLemma
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_ManuscriptCounting
import Theorems.Thm_DeletionCode_CountingLemma_counting_generating_sets

set_option autoImplicit true
open DeletionCode DeletionCode.ManuscriptCounting
open Windows HeaderRecovery CatalogueWords CatalogueBridge SignedSupport
open RuleReconstruction RuleSetGraph SignedRuleCount CountExponent CanonicalIndex

theorem DeletionCode.ManuscriptCounting.counting_generating_sets (t : ℕ) (ht : 1 ≤ t) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (x : Letters) (n k R c : ℕ),
      1 ≤ R → KUnique x n k →
        Nat.card {Q : RuleSet k // GeneratingSet t x n k R c Q} ≤
          n ^ c * (windowLength k * R) ^ (a * R) := by sorry
