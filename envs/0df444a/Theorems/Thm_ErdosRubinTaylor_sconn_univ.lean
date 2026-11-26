-- Prove2me | Theorems.Thm_ErdosRubinTaylor_sconn_univ
-- name    : ErdosRubinTaylor.sconn_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:18.618457+00:00
-- url     : https://prove2.me/theorems/870cb315-a578-5470-a322-40b69d818afb
-- title:
--   Erdos Rubin Taylor: sconn univ
-- statement:
--   The Erdos Rubin Taylor construction uses the sconn univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L111-L119
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L111-L119

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

theorem ErdosRubinTaylor.sconn_univ (hconn : G.Connected) : SConn G Set.univ := by sorry
