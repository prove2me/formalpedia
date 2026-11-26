-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_proper_update2
-- name    : BrooksTheorem.Aux.proper_update2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:46.952685+00:00
-- url     : https://prove2.me/theorems/a39cf6d4-32d3-570a-8d3e-fa02f8660726
-- title:
--   Aux: proper update2
-- statement:
--   Recolour two non-adjacent vertices `x, z` with a common colour `col`.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L224-L246
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L224-L246

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
omit [Fintype V]

theorem BrooksTheorem.Aux.proper_update2 [DecidableEq V] {k : ℕ} {H : SimpleGraph V} (S : Set V) {x z : V}
    (hn : ¬ H.Adj x z)
    (c0 : V → Fin k) (hc0 : Proper (restr H {v | v ∈ S ∧ v ≠ x ∧ v ≠ z}) c0) (col : Fin k)
    (hcol : ∀ w v, (w = x ∨ w = z) → v ∈ S → v ≠ x → v ≠ z → H.Adj w v → c0 v ≠ col) :
    Proper (restr H S) (fun v => if v = x ∨ v = z then col else c0 v) := by sorry
