-- Prove2me | Theorems.Thm_CliqueMinors_exists_low_deg_K3
-- name    : CliqueMinors.exists_low_deg_K3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:41:33.494702+00:00
-- url     : https://prove2.me/theorems/b21a7934-99ec-4d39-925d-97067d5b20c5
-- title:
--   Clique Minors: exists low deg K3
-- statement:
--   The Clique Minors construction uses the exists low deg K3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L650-L655
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L650-L655

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

theorem CliqueMinors.exists_low_deg_K3 (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty)
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G) :
    ∃ v ∈ S, G.degree v < 2 := by sorry
