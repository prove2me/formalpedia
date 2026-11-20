-- Prove2me | Theorems.Thm_DeletionCode_SeparatedTraceCoverage_catalogueRule
-- name    : DeletionCode.SeparatedTraceCoverage.catalogueRule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:58:30.522662+00:00
-- url     : https://prove2.me/theorems/c2907d0f-e6ae-4e6b-9d8a-ee4e2e98cd51
-- title:
--   Separated Trace Coverage: catalogue Rule
-- statement:
--   Manuscript lemma `lem:coverage`: an actual alignment with exactly t
--   deletions and t insertions, separated by 4L matched columns and from both
--   boundaries, has its target-minus-source spectrum in the concrete catalogue.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeparatedTraceCoverage.lean#L22-L82
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeparatedTraceCoverage.lean#L22-L82

import Definitions.Def_DeletionCode_TraceBubbleFamily
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Theorems.Thm_DeletionCode_BubbleCatalogue_catalogueRule

set_option autoImplicit true
open DeletionCode DeletionCode.SeparatedTraceCoverage
open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open SignedSupport RunBubbleConstruction TraceEditData TraceBubbleFamily
open scoped BigOperators

theorem DeletionCode.SeparatedTraceCoverage.catalogueRule (trace : Trace) (t k : ℕ) (hk : 1 ≤ k)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) :
    ConnectedBlocks.CatalogueRule t k
      (wordSpectrum (listLetters trace.target) trace.target.length (windowLength k) -
        wordSpectrum (listLetters trace.source) trace.source.length (windowLength k)) := by sorry
