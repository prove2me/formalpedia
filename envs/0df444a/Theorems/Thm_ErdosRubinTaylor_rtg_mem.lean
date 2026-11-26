-- Prove2me | Theorems.Thm_ErdosRubinTaylor_rtg_mem
-- name    : ErdosRubinTaylor.rtg_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:42.414964+00:00
-- url     : https://prove2.me/theorems/68f90274-8964-5123-8bad-07d7116a8cd0
-- title:
--   Erdos Rubin Taylor: rtg mem
-- statement:
--   The Erdos Rubin Taylor construction uses the rtg mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L58-L61
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L58-L61

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

theorem ErdosRubinTaylor.rtg_mem {u v : V} (h : Relation.ReflTransGen (adjIn G T) u v) (hu : u ∈ T) : v ∈ T := by sorry
