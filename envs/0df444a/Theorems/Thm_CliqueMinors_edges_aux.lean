-- Prove2me | Theorems.Thm_CliqueMinors_edges_aux
-- name    : CliqueMinors.edges_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:39:33.78551+00:00
-- url     : https://prove2.me/theorems/86eba8c0-3a2b-41a9-a38d-82db3b0002a9
-- title:
--   Clique Minors: edges aux
-- statement:
--   The Clique Minors construction uses the edges aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L657-L689
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L657-L689

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
open scoped Classical
variable [Fintype V]

theorem CliqueMinors.edges_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n → 2 ≤ n →
    (∀ a b, G.Adj a b → a ∈ S) → ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G →
    G.edgeFinset.card + 3 ≤ 2 * n := by sorry
