-- Prove2me | Theorems.Thm_ErdosRubinTaylor_degree_induce
-- name    : ErdosRubinTaylor.degree_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:40.878903+00:00
-- url     : https://prove2.me/theorems/184b0b7a-4311-5165-bafa-3edaa0288ea2
-- title:
--   Erdos Rubin Taylor: degree induce
-- statement:
--   Degree in the induced subgraph equals the number of neighbours inside the set.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L187-L198
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L187-L198

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

theorem ErdosRubinTaylor.degree_induce (G : SimpleGraph V) (T : Set V) [Fintype T]
    [DecidableRel (G.induce T).Adj] (v : T) : (G.induce T).degree v = dIn G T v := by sorry
