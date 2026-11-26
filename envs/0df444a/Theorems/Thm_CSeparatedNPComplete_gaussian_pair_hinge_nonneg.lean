-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_pair_hinge_nonneg
-- name    : CSeparatedNPComplete.gaussian_pair_hinge_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:06.218054+00:00
-- url     : https://prove2.me/theorems/385a02a9-94d6-4b68-b07e-35add01b8789
-- title:
--   CSeparated NPComplete: gaussian pair hinge nonneg
-- statement:
--   The CSeparated NPComplete construction uses the gaussian pair hinge nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L93-L94
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L93-L94

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_pair_hinge_nonneg {n : Nat} (c : ℝ) (a : Vec n)
    (g h : Gaussian n) : 0 ≤ gaussian_pair_hinge c a g h := by sorry
