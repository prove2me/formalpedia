-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_mem_of_closed
-- name    : BrooksTheorem.Aux.mem_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:27.09465+00:00
-- url     : https://prove2.me/theorems/c566189a-1bd1-55cf-9050-202290ef074d
-- title:
--   Aux: mem of closed
-- statement:
--   In a connected graph, a set containing a vertex and closed under adjacency is everything.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean#L30-L37
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean#L30-L37

module
public import Definitions.Def_BrooksLib_BrooksCore
public import Definitions.Def_BrooksLib_Cycle
public import Definitions.Def_BrooksLib_BrooksLow
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
omit [Fintype V]

theorem BrooksTheorem.Aux.mem_of_closed (G : SimpleGraph V) (hconn : G.Connected) (C : Set V) {v0 : V}
    (hv0 : v0 ∈ C) (hC : ∀ u ∈ C, ∀ w, G.Adj u w → w ∈ C) (w : V) : w ∈ C := by sorry
