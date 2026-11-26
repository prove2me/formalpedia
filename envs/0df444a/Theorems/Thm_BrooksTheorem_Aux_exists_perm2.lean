-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_exists_perm2
-- name    : BrooksTheorem.Aux.exists_perm2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:21.847734+00:00
-- url     : https://prove2.me/theorems/73181db8-4897-449f-9b2b-7e442c30fe91
-- title:
--   Aux: exists perm2
-- statement:
--   The Aux construction uses the exists perm2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L52-L62
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L52-L62

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}

theorem BrooksTheorem.Aux.exists_perm2 {k : ℕ} {a b a' b' : Fin k} (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ σ : Equiv.Perm (Fin k), σ a = a' ∧ σ b = b' := by sorry
