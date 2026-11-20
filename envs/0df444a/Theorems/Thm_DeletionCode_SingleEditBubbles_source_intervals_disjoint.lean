-- Prove2me | Theorems.Thm_DeletionCode_SingleEditBubbles_source_intervals_disjoint
-- name    : DeletionCode.SingleEditBubbles.source_intervals_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:23.004977+00:00
-- url     : https://prove2.me/theorems/780978b2-0b1e-480a-a718-5c5459f28c3b
-- title:
--   Single Edit Bubbles: source intervals disjoint
-- statement:
--   Two concrete local source intervals inherit disjointness from a 4L gap.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L100-L107
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L100-L107

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation

theorem DeletionCode.SingleEditBubbles.source_intervals_disjoint {k a b : ℕ} {source target₁ target₂ : List Bool}
    {orientation₁ orientation₂ : Orientation}
    (p : RunBubbleConstruction.LocalBubble k source target₁ a orientation₁)
    (q : RunBubbleConstruction.LocalBubble k source target₂ b orientation₂)
    (hgap : a + 4 * windowLength k ≤ b) :
    Disjoint (LocalBubble.sourceInterval p) (LocalBubble.sourceInterval q) := by sorry
