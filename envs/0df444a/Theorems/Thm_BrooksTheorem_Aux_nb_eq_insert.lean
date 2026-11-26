-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_nb_eq_insert
-- name    : BrooksTheorem.Aux.nb_eq_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:56.738632+00:00
-- url     : https://prove2.me/theorems/ba73e1c7-63a3-430e-884f-2d2435620cd7
-- title:
--   Aux: nb eq insert
-- statement:
--   The Aux construction uses the nb eq insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L209-L220
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L209-L220

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
variable [Fintype V]

theorem BrooksTheorem.Aux.nb_eq_insert [DecidableEq V] {H : SimpleGraph V} {k : ℕ} (hdeg : ∀ v, (nb H v).card ≤ k)
    {w p : V}
    {Q : Finset V} (hQ : Q ⊆ nb H w) (hp : H.Adj w p) (hpQ : p ∉ Q) (hcard : k ≤ Q.card + 1) :
    nb H w = insert p Q := by sorry
