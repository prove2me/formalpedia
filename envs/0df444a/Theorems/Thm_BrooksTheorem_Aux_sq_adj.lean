-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_sq_adj
-- name    : BrooksTheorem.Aux.sq_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:50.858995+00:00
-- url     : https://prove2.me/theorems/2075e842-d72a-4dde-a646-429d27cff85b
-- title:
--   Aux: sq adj
-- statement:
--   The Aux construction uses the sq adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L59-L62
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L59-L62

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

theorem BrooksTheorem.Aux.sq_adj (n : ℕ) : G.Adj (sq G v0 v1 n) (sq G v0 v1 (n + 1)) := by sorry
