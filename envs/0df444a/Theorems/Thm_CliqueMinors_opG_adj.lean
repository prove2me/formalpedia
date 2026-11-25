-- Prove2me | Theorems.Thm_CliqueMinors_opG_adj
-- name    : CliqueMinors.opG_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:39.172628+00:00
-- url     : https://prove2.me/theorems/5d8bfe84-f6fd-52eb-bc39-fed0058adfd2
-- title:
--   Clique Minors: op G adj
-- statement:
--   The Clique Minors construction uses the op G adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L238-L241
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L238-L241

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

theorem CliqueMinors.opG_adj {G : SimpleGraph V} {x b a c u v : V} :
    (opG G x b a c).Adj u v ↔ u ≠ v ∧ u ≠ x ∧ u ≠ b ∧ v ≠ x ∧ v ≠ b ∧
      (G.Adj u v ∨ (u = a ∧ v = c) ∨ (u = c ∧ v = a)) := by sorry
