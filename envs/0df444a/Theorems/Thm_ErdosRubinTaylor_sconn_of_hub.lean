-- Prove2me | Theorems.Thm_ErdosRubinTaylor_sconn_of_hub
-- name    : ErdosRubinTaylor.sconn_of_hub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:09.573086+00:00
-- url     : https://prove2.me/theorems/0ae91681-e8d7-51cf-95fc-dcf36ec2d71e
-- title:
--   Erdos Rubin Taylor: sconn of hub
-- statement:
--   A set is connected as soon as every vertex is joined to a fixed vertex.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L80-L82
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L80-L82

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

theorem ErdosRubinTaylor.sconn_of_hub {a : V} (ha : a ∈ T)
    (h : ∀ v ∈ T, Relation.ReflTransGen (adjIn G T) a v) : SConn G T := by sorry
