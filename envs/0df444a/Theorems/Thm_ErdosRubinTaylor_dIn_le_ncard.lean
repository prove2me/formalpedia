-- Prove2me | Theorems.Thm_ErdosRubinTaylor_dIn_le_ncard
-- name    : ErdosRubinTaylor.dIn_le_ncard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:37.624556+00:00
-- url     : https://prove2.me/theorems/044f7c30-6165-5318-a9a7-ed5d8b3780c0
-- title:
--   Erdos Rubin Taylor: d In le ncard
-- statement:
--   The Erdos Rubin Taylor construction uses the d In le ncard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L145-L155
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L145-L155

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

theorem ErdosRubinTaylor.dIn_le_ncard (G : SimpleGraph V) (T : Set V) {v : V} (hv : v ∈ T) :
    dIn G T v ≤ T.ncard - 1 := by sorry
