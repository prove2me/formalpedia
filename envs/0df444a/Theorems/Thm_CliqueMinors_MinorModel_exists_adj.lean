-- Prove2me | Theorems.Thm_CliqueMinors_MinorModel_exists_adj
-- name    : CliqueMinors.MinorModel.exists_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:39:03.326517+00:00
-- url     : https://prove2.me/theorems/f213976d-9e12-4054-b877-e98692259210
-- title:
--   Minor Model: exists adj
-- statement:
--   The Minor Model construction uses the exists adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L93-L103
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L93-L103

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation

theorem CliqueMinors.MinorModel.exists_adj {G : SimpleGraph V} {r : ℕ}
    (M : MinorModel G (⊤ : SimpleGraph (Fin r))) (hr : 2 ≤ r) (i : Fin r) {v : V}
    (hv : v ∈ M.branch i) : ∃ u, G.Adj v u := by sorry
