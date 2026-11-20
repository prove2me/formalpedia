-- Prove2me | Theorems.Thm_DeletionCode_LocalBubbleDisjoint_vertices_disjoint_of_gap
-- name    : DeletionCode.LocalBubbleDisjoint.vertices_disjoint_of_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:44:47.659398+00:00
-- url     : https://prove2.me/theorems/eff5c0bb-d967-4b11-bd82-62f54e907876
-- title:
--   Local Bubble Disjoint: vertices disjoint of gap
-- statement:
--   The Local Bubble Disjoint construction uses the vertices disjoint of gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L151-L158
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/LocalBubbleDisjoint.lean#L151-L158

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.LocalBubbleDisjoint.vertices_disjoint_of_gap {a b : ℕ} {target₁ target₂ : List Bool}
    {orientation₁ orientation₂ : Orientation} (hk : 1 ≤ k)
    (hx : KUnique (listLetters source) source.length k)
    (p : LocalBubble k source target₁ a orientation₁)
    (q : LocalBubble k source target₂ b orientation₂)
    (hgap : a + 4 * windowLength k ≤ b) (side₁ side₂ : Bool) :
    Disjoint (vertices p side₁) (vertices q side₂) := by sorry
