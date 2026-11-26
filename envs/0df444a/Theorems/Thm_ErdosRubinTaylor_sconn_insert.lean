-- Prove2me | Theorems.Thm_ErdosRubinTaylor_sconn_insert
-- name    : ErdosRubinTaylor.sconn_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:11.712722+00:00
-- url     : https://prove2.me/theorems/420b320e-3598-5b17-b901-a4f459dae535
-- title:
--   Erdos Rubin Taylor: sconn insert
-- statement:
--   The Erdos Rubin Taylor construction uses the sconn insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L85-L95
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L85-L95

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}

theorem ErdosRubinTaylor.sconn_insert {W D : Set V} {x : V} (hDW : D ⊆ W)
    (hcl : ∀ u ∈ D, ∀ v ∈ W, G.Adj u v → v ∈ D)
    (hreach : ∀ v ∈ W, ∃ c ∈ W, G.Adj c x ∧ Relation.ReflTransGen (adjIn G W) v c) :
    SConn G (insert x D) := by sorry
