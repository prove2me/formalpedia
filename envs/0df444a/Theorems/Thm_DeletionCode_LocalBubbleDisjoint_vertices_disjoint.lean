-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_vertices_disjoint
-- name    : DeletionCode.LocalBubbleDisjoint.vertices_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:44:51.81821+00:00
-- url     : https://prove2.me/theorems/d48675e6-e7ab-45ae-9657-c70fd39be1d6
-- title:
--   Local Bubble Disjoint: vertices disjoint
-- statement:
--   Actual cross-bubble vertex disjointness, simultaneously for both path
--   sides and including endpoints. Only source interval disjointness is supplied.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L121-L135
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L121-L135

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.vertices_disjoint {a b : ℕ} {target₁ target₂ : List Bool}
    {orientation₁ orientation₂ : Orientation} (hk : 1 ≤ k)
    (hx : KUnique (listLetters source) source.length k)
    (p : LocalBubble k source target₁ a orientation₁)
    (q : LocalBubble k source target₂ b orientation₂)
    (hdis : Disjoint (SingleEditBubbles.LocalBubble.sourceInterval p)
      (SingleEditBubbles.LocalBubble.sourceInterval q)) (side₁ side₂ : Bool) :
    Disjoint (vertices p side₁) (vertices q side₂) := by sorry
