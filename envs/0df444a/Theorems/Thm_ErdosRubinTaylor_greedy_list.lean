-- Prove2me | Theorems.Thm_ErdosRubinTaylor_greedy_list
-- name    : ErdosRubinTaylor.greedy_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:43.533338+00:00
-- url     : https://prove2.me/theorems/ea67ba4f-7ef6-59f5-88f6-c9cd561d3361
-- title:
--   Erdos Rubin Taylor: greedy list
-- statement:
--   Greedy list colouring: colour the vertices of `U` in order of non-increasing rank `r`.
--   It suffices that each vertex has fewer neighbours in `U` of rank at least its own than
--   colours in its list.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L206-L250
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L206-L250

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]
open Classical

theorem ErdosRubinTaylor.greedy_list {C : Type*} [Nonempty C] (G : SimpleGraph V)
    (L : V → Finset C) (r : V → ℕ) (U : Finset V)
    (hU : ∀ w ∈ U, (univ.filter (fun u => u ∈ U ∧ G.Adj w u ∧ r w ≤ r u)).card < (L w).card) :
    ∃ g : V → C, (∀ v ∈ U, g v ∈ L v) ∧ ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → g u ≠ g v := by sorry
