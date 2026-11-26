-- Prove2me | Theorems.Thm_CSeparatedNPComplete_hinge_against_eq_zero
-- name    : CSeparatedNPComplete.hinge_against_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:15.144834+00:00
-- url     : https://prove2.me/theorems/76d1b93d-65fd-48a8-a47d-b4bc828419a2
-- title:
--   CSeparated NPComplete: hinge against eq zero
-- statement:
--   The CSeparated NPComplete construction uses the hinge against eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L108-L115
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L108-L115

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.hinge_against_eq_zero {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n)
    (L : List (Gaussian n))
    (h : ∀ b ∈ L, gaussian_pair_hinge c a g b = 0) : hinge_against c a g L = 0 := by sorry
