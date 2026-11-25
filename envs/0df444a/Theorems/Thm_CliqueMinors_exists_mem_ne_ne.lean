-- Prove2me | Theorems.Thm_CliqueMinors_exists_mem_ne_ne
-- name    : CliqueMinors.exists_mem_ne_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:36.634733+00:00
-- url     : https://prove2.me/theorems/2354fdec-725f-54c5-a77b-2de70d313a5b
-- title:
--   Clique Minors: exists mem ne ne
-- statement:
--   The Clique Minors construction uses the exists mem ne ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L198-L204
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L198-L204

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]

theorem CliqueMinors.exists_mem_ne_ne {s : Finset V} (h : 3 ≤ s.card) (p q : V) :
    ∃ z ∈ s, z ≠ p ∧ z ≠ q := by sorry
