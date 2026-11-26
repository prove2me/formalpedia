-- Prove2me | Theorems.Thm_ErdosRubinTaylor_adjIn_symm
-- name    : ErdosRubinTaylor.adjIn_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:14.004019+00:00
-- url     : https://prove2.me/theorems/2e04e513-1942-4035-8360-1d09558dc8a4
-- title:
--   Erdos Rubin Taylor: adj In symm
-- statement:
--   The Erdos Rubin Taylor construction uses the adj In symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L44-L44
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L44-L44

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

theorem ErdosRubinTaylor.adjIn_symm {u v : V} (h : adjIn G T u v) : adjIn G T v u := by sorry
