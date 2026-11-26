-- Prove2me | Theorems.Thm_ErdosRubinTaylor_rtg_closed
-- name    : ErdosRubinTaylor.rtg_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:50.433313+00:00
-- url     : https://prove2.me/theorems/01136016-3c44-5092-913f-81961ab69bce
-- title:
--   Erdos Rubin Taylor: rtg closed
-- statement:
--   Closure lemma: if `D ⊆ W` is closed under adjacency inside `W`, paths in `W` starting in `D`
--   stay in `D`.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L65-L74
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L65-L74

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable {G : SimpleGraph V} {T T' : Set V}

theorem ErdosRubinTaylor.rtg_closed {W D : Set V}
    (hcl : ∀ u ∈ D, ∀ v ∈ W, G.Adj u v → v ∈ D) {u v : V}
    (h : Relation.ReflTransGen (adjIn G W) u v) (hu : u ∈ D) :
    Relation.ReflTransGen (adjIn G D) u v ∧ v ∈ D := by sorry
