-- Prove2me | Theorems.Thm_ErdosRubinTaylor_reach_cut
-- name    : ErdosRubinTaylor.reach_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:13.701507+00:00
-- url     : https://prove2.me/theorems/4860c67b-f308-4965-aa62-e4f4ee564d2b
-- title:
--   Erdos Rubin Taylor: reach cut
-- statement:
--   From a vertex `v ≠ x` of a connected set `T`, some neighbour of `x` can be reached inside
--   `T − x`.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L68-L83
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L68-L83

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}

theorem ErdosRubinTaylor.reach_cut {T : Set V} (hT : SConn G T) {x : V} (hx : x ∈ T) {v : V} (hv : v ∈ T \ {x}) :
    ∃ c ∈ T \ {x}, G.Adj c x ∧ Relation.ReflTransGen (adjIn G (T \ {x})) v c := by sorry
