-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_nb_sq
-- name    : BrooksTheorem.Aux.nb_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:50.567805+00:00
-- url     : https://prove2.me/theorems/975aa029-9056-5aad-a610-eb4ad559736f
-- title:
--   Aux: nb sq
-- statement:
--   The Aux construction uses the nb sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L69-L78
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L69-L78

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_Cycle
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) (h2 : ∀ v, (nb G v).card = 2) (v0 v1 : V) (h01 : G.Adj v0 v1)
include h2 h01

theorem BrooksTheorem.Aux.nb_sq [DecidableEq V] (n : ℕ) :
    nb G (sq G v0 v1 (n + 1)) = {sq G v0 v1 n, sq G v0 v1 (n + 2)} := by sorry
