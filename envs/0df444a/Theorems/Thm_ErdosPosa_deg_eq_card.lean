-- Prove2me | Theorems.Thm_ErdosPosa_deg_eq_card
-- name    : ErdosPosa.deg_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:22:09.722161+00:00
-- url     : https://prove2.me/theorems/168445a6-322e-5b7a-8d4e-dc1a06cafd06
-- title:
--   Erdos Posa: deg eq card
-- statement:
--   The Erdos Posa construction uses the deg eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L101-L105
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L101-L105

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*} {H : SimpleGraph V}

theorem ErdosPosa.deg_eq_card [Fintype V] [DecidableRel H.Adj] (x : V) :
    deg H x = (Finset.univ.filter (fun y => H.Adj x y)).card := by sorry
