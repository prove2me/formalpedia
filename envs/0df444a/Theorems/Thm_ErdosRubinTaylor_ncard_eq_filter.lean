-- Prove2me | Theorems.Thm_ErdosRubinTaylor_ncard_eq_filter
-- name    : ErdosRubinTaylor.ncard_eq_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:16.019357+00:00
-- url     : https://prove2.me/theorems/bf365fea-197b-54d3-84c4-162206c439cf
-- title:
--   Erdos Rubin Taylor: ncard eq filter
-- statement:
--   The Erdos Rubin Taylor construction uses the ncard eq filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L141-L143
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L141-L143

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

theorem ErdosRubinTaylor.ncard_eq_filter (T : Set V) [DecidablePred (· ∈ T)] :
    T.ncard = (univ.filter (· ∈ T)).card := by sorry
