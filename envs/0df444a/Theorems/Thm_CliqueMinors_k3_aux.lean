-- Prove2me | Theorems.Thm_CliqueMinors_k3_aux
-- name    : CliqueMinors.k3_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:41:34.749744+00:00
-- url     : https://prove2.me/theorems/3a3cc451-44d9-4af9-953e-d4ec25d3d140
-- title:
--   Clique Minors: k3 aux
-- statement:
--   The Clique Minors construction uses the k3 aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L608-L641
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L608-L641

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

theorem CliqueMinors.k3_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n → S.Nonempty →
    (∀ a b, G.Adj a b → a ∈ S) → (∀ v ∈ S, 2 ≤ G.degree v) →
    IsMinor (⊤ : SimpleGraph (Fin 3)) G := by sorry
