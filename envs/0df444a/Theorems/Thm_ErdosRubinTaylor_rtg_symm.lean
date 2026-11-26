-- Prove2me | Theorems.Thm_ErdosRubinTaylor_rtg_symm
-- name    : ErdosRubinTaylor.rtg_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:21.749159+00:00
-- url     : https://prove2.me/theorems/463aa5e4-9181-4972-a501-092d9fbb11d5
-- title:
--   Erdos Rubin Taylor: rtg symm
-- statement:
--   The Erdos Rubin Taylor construction uses the rtg symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L46-L50
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L46-L50

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

theorem ErdosRubinTaylor.rtg_symm {u v : V} (h : Relation.ReflTransGen (adjIn G T) u v) :
    Relation.ReflTransGen (adjIn G T) v u := by sorry
