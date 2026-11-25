-- Prove2me | Theorems.Thm_CliqueMinors_isMinor_lift_cone
-- name    : CliqueMinors.isMinor_lift_cone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:39:07.075748+00:00
-- url     : https://prove2.me/theorems/263d22ba-2039-5030-a7d4-358a36b1cd07
-- title:
--   Clique Minors: is Minor lift cone
-- statement:
--   The Clique Minors construction uses the is Minor lift cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L184-L226
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L184-L226

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

theorem CliqueMinors.isMinor_lift_cone {G G' : SimpleGraph V} {x : V}
    (hG' : ∀ u v, G'.Adj u v → G.Adj u v ∧ G.Adj x u ∧ G.Adj x v)
    {r : ℕ} (hr : 2 ≤ r) (h : IsMinor (⊤ : SimpleGraph (Fin r)) G') :
    IsMinor (⊤ : SimpleGraph (Fin (r + 1))) G := by sorry
