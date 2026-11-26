-- Prove2me | Theorems.Thm_ErdosRubinTaylor_connected_iff_sconn
-- name    : ErdosRubinTaylor.connected_iff_sconn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:21.284043+00:00
-- url     : https://prove2.me/theorems/998b3307-c673-4077-b6d6-086aa024dbdc
-- title:
--   Erdos Rubin Taylor: connected iff sconn
-- statement:
--   The Erdos Rubin Taylor construction uses the connected iff sconn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L84-L109
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L84-L109

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

theorem ErdosRubinTaylor.connected_iff_sconn : (G.induce T).Connected ↔ SConn G T := by sorry
