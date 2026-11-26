-- Prove2me | Theorems.Thm_ErdosRubinTaylor_exists_rank
-- name    : ErdosRubinTaylor.exists_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:01.839237+00:00
-- url     : https://prove2.me/theorems/7356ba09-58a5-5ad0-b933-9d4ec1cc014b
-- title:
--   Erdos Rubin Taylor: exists rank
-- statement:
--   The Erdos Rubin Taylor construction uses the exists rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L262-L279
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L262-L279

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}

theorem ErdosRubinTaylor.exists_rank (G : SimpleGraph V) (W Tgt : Set V)
    (h : ∀ v ∈ W, ∃ n, near G W Tgt n v) :
    ∃ r : V → ℕ, ∀ v ∈ W, v ∉ Tgt → ∃ u ∈ W, G.Adj v u ∧ r u < r v := by sorry
