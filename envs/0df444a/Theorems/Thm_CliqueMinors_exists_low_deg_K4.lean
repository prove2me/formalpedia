-- Prove2me | Theorems.Thm_CliqueMinors_exists_low_deg_K4
-- name    : CliqueMinors.exists_low_deg_K4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:32.38839+00:00
-- url     : https://prove2.me/theorems/8a6a331f-bb41-5fb9-8d83-6150613b45ff
-- title:
--   Clique Minors: exists low deg K4
-- statement:
--   The Clique Minors construction uses the exists low deg K4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L643-L648
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L643-L648

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

theorem CliqueMinors.exists_low_deg_K4 (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty)
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) :
    ∃ v ∈ S, G.degree v < 3 := by sorry
