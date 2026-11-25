-- Prove2me | Theorems.Thm_CliqueMinors_isMinor_of_clique
-- name    : CliqueMinors.isMinor_of_clique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:22.394076+00:00
-- url     : https://prove2.me/theorems/cde32a3f-9b46-5776-813c-49d1315e1e10
-- title:
--   Clique Minors: is Minor of clique
-- statement:
--   The Clique Minors construction uses the is Minor of clique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L113-L119
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L113-L119

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
open Relation

theorem CliqueMinors.isMinor_of_clique {G : SimpleGraph V} {r : ℕ} (f : Fin r → V)
    (hf : ∀ i j, i ≠ j → G.Adj (f i) (f j)) : IsMinor (⊤ : SimpleGraph (Fin r)) G := by sorry
