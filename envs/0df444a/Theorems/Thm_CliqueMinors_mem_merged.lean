-- Prove2me | Theorems.Thm_CliqueMinors_mem_merged
-- name    : CliqueMinors.mem_merged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:42.83126+00:00
-- url     : https://prove2.me/theorems/144afe8a-16cc-49ea-bda0-69b1dc22c47e
-- title:
--   Clique Minors: mem merged
-- statement:
--   The Clique Minors construction uses the mem merged property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L221-L224
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L221-L224

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

theorem CliqueMinors.mem_merged {G : SimpleGraph V} {x y t : V} :
    t ∈ ((G.neighborFinset x ∪ G.neighborFinset y).erase x).erase y ↔
      t ≠ y ∧ t ≠ x ∧ (G.Adj x t ∨ G.Adj y t) := by sorry
