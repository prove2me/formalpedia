-- Prove2me | Theorems.Thm_ErdosRubinTaylor_two_le_ncard_insert
-- name    : ErdosRubinTaylor.two_le_ncard_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:19.552494+00:00
-- url     : https://prove2.me/theorems/ebc0491c-8254-4d93-b7fe-b5c114c5c60e
-- title:
--   Erdos Rubin Taylor: two le ncard insert
-- statement:
--   The Erdos Rubin Taylor construction uses the two le ncard insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L60-L64
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L60-L64

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}

theorem ErdosRubinTaylor.two_le_ncard_insert [Finite V] {D : Set V} {x b : V} (hb : b ∈ D) (hxb : x ≠ b) :
    2 ≤ (insert x D).ncard := by sorry
