-- Prove2me | Theorems.Thm_CSeparatedNPComplete_convexOnPredicate_iff_convexOn
-- name    : CSeparatedNPComplete.convexOnPredicate_iff_convexOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:46:20.061111+00:00
-- url     : https://prove2.me/theorems/73075bfb-f25a-4c30-9807-b182ccdc4929
-- title:
--   CSeparated NPComplete: convex On Predicate iff convex On
-- statement:
--   The source's bundled convexity condition is exactly mathlib's `ConvexOn`.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/ConvexPredicate.lean#L12-L26
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/ConvexPredicate.lean#L12-L26

module
public import Definitions.Def_CSeparatedNPComplete_Definitions
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.Linarith
public import Definitions.Def_CSeparatedNPComplete_ConvexPredicate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.convexOnPredicate_iff_convexOn (P : Real → Prop) (f : Real → Real) :
    convexOnPredicate P f ↔ ConvexOn ℝ {x | P x} f := by sorry
