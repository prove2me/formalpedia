-- Prove2me | Theorems.Thm_DeletionCode_SingleEditBubbles_source_intervals_disjoint_of_trace
-- name    : DeletionCode.SingleEditBubbles.source_intervals_disjoint_of_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:25.2158+00:00
-- url     : https://prove2.me/theorems/bcdfb578-043f-4448-a7ae-1c3ef0ddfd7c
-- title:
--   Single Edit Bubbles: source intervals disjoint of trace
-- statement:
--   The separated alignment supplies the gap for the constructed source intervals.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L110-L119
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L110-L119

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation

theorem DeletionCode.SingleEditBubbles.source_intervals_disjoint_of_trace {k : ℕ} {trace : AlignmentTrace.Trace}
    (hsep : FiniteConflictGraph.Separated (4 * windowLength k) trace)
    (i j : Fin trace.length) (hi : FiniteConflictGraph.EditIndex trace i)
    (hj : FiniteConflictGraph.EditIndex trace j) (hne : i ≠ j)
    {target₁ target₂ : List Bool} {orientation₁ orientation₂ : Orientation}
    (p : RunBubbleConstruction.LocalBubble k trace.source target₁ (trace.sourcePosition i.val) orientation₁)
    (q : RunBubbleConstruction.LocalBubble k trace.source target₂ (trace.sourcePosition j.val) orientation₂) :
    Disjoint (LocalBubble.sourceInterval p) (LocalBubble.sourceInterval q) := by sorry
