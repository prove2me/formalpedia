-- Prove2me | Theorems.Thm_ErdosRubinTaylor_rtg_mono
-- name    : ErdosRubinTaylor.rtg_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:46.640782+00:00
-- url     : https://prove2.me/theorems/dce51d1b-f1ea-4bce-ae03-0a3804bc8b46
-- title:
--   Erdos Rubin Taylor: rtg mono
-- statement:
--   The Erdos Rubin Taylor construction uses the rtg mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L52-L56
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L52-L56

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

theorem ErdosRubinTaylor.rtg_mono (hTT : T ⊆ T') {u v : V} (h : Relation.ReflTransGen (adjIn G T) u v) :
    Relation.ReflTransGen (adjIn G T') u v := by sorry
