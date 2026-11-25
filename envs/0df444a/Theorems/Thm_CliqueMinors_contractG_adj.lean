-- Prove2me | Theorems.Thm_CliqueMinors_contractG_adj
-- name    : CliqueMinors.contractG_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:13.270317+00:00
-- url     : https://prove2.me/theorems/bf4a0ee9-9572-4116-a2ae-2f961fa134de
-- title:
--   Clique Minors: contract G adj
-- statement:
--   The Clique Minors construction uses the contract G adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L44-L47
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L44-L47

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

theorem CliqueMinors.contractG_adj {G : SimpleGraph V} {x y a b : V} :
    (contractG G x y).Adj a b ↔
      a ≠ b ∧ a ≠ y ∧ b ≠ y ∧ (G.Adj a b ∨ (a = x ∧ G.Adj y b) ∨ (b = x ∧ G.Adj y a)) := by sorry
