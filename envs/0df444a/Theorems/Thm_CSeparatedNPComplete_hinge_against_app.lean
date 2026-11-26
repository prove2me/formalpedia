-- Prove2me | Theorems.Thm_CSeparatedNPComplete_hinge_against_app
-- name    : CSeparatedNPComplete.hinge_against_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:46:41.359628+00:00
-- url     : https://prove2.me/theorems/1091e2a8-a109-5784-abd5-5385a52e337a
-- title:
--   CSeparated NPComplete: hinge against app
-- statement:
--   The CSeparated NPComplete construction uses the hinge against app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L117-L122
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L117-L122

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.hinge_against_app {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n)
    (L₁ L₂ : List (Gaussian n)) :
    hinge_against c a g (L₁ ++ L₂) = hinge_against c a g L₁ + hinge_against c a g L₂ := by sorry
