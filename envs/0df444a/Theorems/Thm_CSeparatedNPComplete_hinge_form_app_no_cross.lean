-- Prove2me | Theorems.Thm_CSeparatedNPComplete_hinge_form_app_no_cross
-- name    : CSeparatedNPComplete.hinge_form_app_no_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:21.842898+00:00
-- url     : https://prove2.me/theorems/69eb3af6-fd2f-59fb-9736-2350d1c131f3
-- title:
--   CSeparated NPComplete: hinge form app no cross
-- statement:
--   The CSeparated NPComplete construction uses the hinge form app no cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L124-L132
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L124-L132

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.hinge_form_app_no_cross {n : Nat} (c : ℝ) (a : Vec n)
    (L₁ L₂ : List (Gaussian n)) (h : ∀ g ∈ L₁, hinge_against c a g L₂ = 0) :
    hinge_form c a (L₁ ++ L₂) = hinge_form c a L₁ + hinge_form c a L₂ := by sorry
