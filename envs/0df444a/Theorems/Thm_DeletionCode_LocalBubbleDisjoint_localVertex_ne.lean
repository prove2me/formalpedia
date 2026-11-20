-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_localVertex_ne
-- name    : DeletionCode.LocalBubbleDisjoint.localVertex_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:45:28.994053+00:00
-- url     : https://prove2.me/theorems/23b8ba09-ef9a-4adb-87b2-7884f374decc
-- title:
--   Local Bubble Disjoint: local Vertex ne
-- statement:
--   The Local Bubble Disjoint construction uses the local Vertex ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L137-L149
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L137-L149

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.localVertex_ne {a b : ℕ} {target₁ target₂ : List Bool}
    {orientation₁ orientation₂ : Orientation} (hk : 1 ≤ k)
    (hx : KUnique (listLetters source) source.length k)
    (p : LocalBubble k source target₁ a orientation₁)
    (q : LocalBubble k source target₂ b orientation₂)
    (hdis : Disjoint (SingleEditBubbles.LocalBubble.sourceInterval p)
      (SingleEditBubbles.LocalBubble.sourceInterval q)) (side₁ side₂ : Bool) (i j : ℕ)
    (hi : i + (windowLength k - 1) ≤ (pathWord p side₁).length)
    (hj : j + (windowLength k - 1) ≤ (pathWord q side₂).length) :
    localVertex p side₁ i ≠ localVertex q side₂ j := by sorry
