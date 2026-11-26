-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_exists_cycle_equiv
-- name    : BrooksTheorem.Aux.exists_cycle_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:57.639213+00:00
-- url     : https://prove2.me/theorems/d5395dce-32c4-4070-a47d-7db754bdf37c
-- title:
--   Aux: exists cycle equiv
-- statement:
--   A connected graph in which all vertices have exactly two neighbours is a cycle: there is
--   `n` and a bijection `Fin (n + 3) ≃ V` mapping the cycle edges to edges of `G`.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L84-L202
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L84-L202

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

theorem BrooksTheorem.Aux.exists_cycle_equiv (G : SimpleGraph V) (hconn : G.Connected)
    (h2 : ∀ v, (nb G v).card = 2) :
    ∃ n, ∃ e : Fin (n + 3) ≃ V, ∀ i j, (cycleGraph (n + 3)).Adj i j → G.Adj (e i) (e j) := by sorry
