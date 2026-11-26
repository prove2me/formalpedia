-- Prove2me | Theorems.Thm_ErdosRubinTaylor_ncard_eq_of_iso
-- name    : ErdosRubinTaylor.ncard_eq_of_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:34.71426+00:00
-- url     : https://prove2.me/theorems/8da07018-6bda-4d38-9540-34255f4c8f0a
-- title:
--   Erdos Rubin Taylor: ncard eq of iso
-- statement:
--   The Erdos Rubin Taylor construction uses the ncard eq of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L205-L210
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L205-L210

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V]
omit [Fintype V]

theorem ErdosRubinTaylor.ncard_eq_of_iso [Finite V] {T : Set V} {n : ℕ} (e : G.induce T ≃g cycleGraph n) :
    T.ncard = n := by sorry
