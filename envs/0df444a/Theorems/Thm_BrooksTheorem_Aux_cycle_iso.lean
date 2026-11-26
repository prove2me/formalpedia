-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_cycle_iso
-- name    : BrooksTheorem.Aux.cycle_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:54.223408+00:00
-- url     : https://prove2.me/theorems/8fc41ee5-e3a5-403c-a90f-4e57f3f428fb
-- title:
--   Aux: cycle iso
-- statement:
--   Upgrading an edge-preserving bijection from a cycle onto a graph with all degrees two to an
--   isomorphism.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L206-L245
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L206-L245

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

theorem BrooksTheorem.Aux.cycle_iso (G : SimpleGraph V) (h2 : ∀ v, (nb G v).card = 2) (n : ℕ)
    (e : Fin (n + 3) ≃ V) (he : ∀ i j, (cycleGraph (n + 3)).Adj i j → G.Adj (e i) (e j)) :
    Nonempty (G ≃g cycleGraph (n + 3)) := by sorry
