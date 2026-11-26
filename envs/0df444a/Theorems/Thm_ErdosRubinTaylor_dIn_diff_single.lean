-- Prove2me | Theorems.Thm_ErdosRubinTaylor_dIn_diff_single
-- name    : ErdosRubinTaylor.dIn_diff_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:42.335941+00:00
-- url     : https://prove2.me/theorems/1ace2082-dcbe-5013-a948-db98cca5d966
-- title:
--   Erdos Rubin Taylor: d In diff single
-- statement:
--   The Erdos Rubin Taylor construction uses the d In diff single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L158-L184
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L158-L184

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
open Classical

theorem ErdosRubinTaylor.dIn_diff_single (G : SimpleGraph V) {T : Set V} {u : V} (hu : u ∈ T) (x : V) :
    dIn G T x = dIn G (T \ {u}) x + if G.Adj x u then 1 else 0 := by sorry
