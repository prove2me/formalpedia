-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_localVertex_ne_of_trace
-- name    : DeletionCode.LocalBubbleDisjoint.localVertex_ne_of_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:45:26.028214+00:00
-- url     : https://prove2.me/theorems/2d4d31b4-f526-4952-9095-3364e7ef2d59
-- title:
--   Local Bubble Disjoint: local Vertex ne of trace
-- statement:
--   The Local Bubble Disjoint construction uses the local Vertex ne of trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L172-L186
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L172-L186

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.localVertex_ne_of_trace {trace : AlignmentTrace.Trace} (hk : 1 ≤ k)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : FiniteConflictGraph.Separated (4 * windowLength k) trace)
    (i j : Fin trace.length) (hi : FiniteConflictGraph.EditIndex trace i)
    (hj : FiniteConflictGraph.EditIndex trace j) (hne : i ≠ j)
    {target₁ target₂ : List Bool} {orientation₁ orientation₂ : Orientation}
    (p : LocalBubble k trace.source target₁ (trace.sourcePosition i.val) orientation₁)
    (q : LocalBubble k trace.source target₂ (trace.sourcePosition j.val) orientation₂)
    (side₁ side₂ : Bool) (a b : ℕ)
    (ha : a + (windowLength k - 1) ≤ (pathWord p side₁).length)
    (hb : b + (windowLength k - 1) ≤ (pathWord q side₂).length) :
    localVertex p side₁ a ≠ localVertex q side₂ b := by sorry
