-- Prove2me | Theorems.Thm_ErdosRubinTaylor_SConn_rtg
-- name    : ErdosRubinTaylor.SConn.rtg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:14.368886+00:00
-- url     : https://prove2.me/theorems/9daa801a-4eaf-51f8-a432-7d7c768dadd3
-- title:
--   SConn: rtg
-- statement:
--   The SConn construction uses the rtg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L76-L77
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L76-L77

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

theorem ErdosRubinTaylor.SConn.rtg (h : SConn G T) {u v : V} (hu : u ∈ T) (hv : v ∈ T) :
    Relation.ReflTransGen (adjIn G T) u v := by sorry
