-- Prove2me | Theorems.Thm_CliqueMinors_mader_five_aux
-- name    : CliqueMinors.mader_five_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:41:52.295855+00:00
-- url     : https://prove2.me/theorems/feddfe66-46bd-581d-8c4d-0c917588a753
-- title:
--   Clique Minors: mader five aux
-- statement:
--   The Clique Minors construction uses the mader five aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L76-L149
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L76-L149

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]

theorem CliqueMinors.mader_five_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n →
    (∀ a b, G.Adj a b → a ∈ S) → 3 ≤ n → 3 * n ≤ G.edgeFinset.card + 5 →
    IsMinor (⊤ : SimpleGraph (Fin 5)) G := by sorry
