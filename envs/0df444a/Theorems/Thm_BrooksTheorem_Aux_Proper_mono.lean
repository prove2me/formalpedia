-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_Proper_mono
-- name    : BrooksTheorem.Aux.Proper.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:18.452031+00:00
-- url     : https://prove2.me/theorems/bff6f7ae-1a1f-48c4-bf5b-0569efdafaca
-- title:
--   Proper: mono
-- statement:
--   The Proper construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L48-L50
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L48-L50

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

theorem BrooksTheorem.Aux.Proper.mono {k : ℕ} {H H' : SimpleGraph V} {f : V → Fin k} (hf : Proper H f)
    (hle : H' ≤ H) : Proper H' f := by sorry
