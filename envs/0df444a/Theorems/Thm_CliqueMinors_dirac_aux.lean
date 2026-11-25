-- Prove2me | Theorems.Thm_CliqueMinors_dirac_aux
-- name    : CliqueMinors.dirac_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:40:26.529216+00:00
-- url     : https://prove2.me/theorems/33a99252-c259-42d5-bdec-67e630462e63
-- title:
--   Clique Minors: dirac aux
-- statement:
--   The Clique Minors construction uses the dirac aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L529-L598
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L529-L598

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

theorem CliqueMinors.dirac_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n → S.Nonempty →
    (∀ a b, G.Adj a b → a ∈ S) → (∀ v ∈ S, 3 ≤ G.degree v) →
    IsMinor (⊤ : SimpleGraph (Fin 4)) G := by sorry
