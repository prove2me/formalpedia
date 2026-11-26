-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_Proper_comp
-- name    : BrooksTheorem.Aux.Proper.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:08.916343+00:00
-- url     : https://prove2.me/theorems/d0c72c73-d9e2-4a81-8adf-ed2ecbb9e1fc
-- title:
--   Proper: comp
-- statement:
--   The Proper construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L44-L46
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L44-L46

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

theorem BrooksTheorem.Aux.Proper.comp {k : ℕ} {H : SimpleGraph V} {f : V → Fin k} (hf : Proper H f)
    (σ : Equiv.Perm (Fin k)) : Proper H (σ ∘ f) := by sorry
