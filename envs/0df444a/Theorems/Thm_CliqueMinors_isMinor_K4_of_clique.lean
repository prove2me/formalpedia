-- Prove2me | Theorems.Thm_CliqueMinors_isMinor_K4_of_clique
-- name    : CliqueMinors.isMinor_K4_of_clique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:39:37.553289+00:00
-- url     : https://prove2.me/theorems/3485281b-0dc6-4049-a0c8-c45c565e9088
-- title:
--   Clique Minors: is Minor K4 of clique
-- statement:
--   The Clique Minors construction uses the is Minor K4 of clique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L304-L309
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L304-L309

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
omit [Fintype V]

theorem CliqueMinors.isMinor_K4_of_clique {G : SimpleGraph V} {x a b c : V} (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hxc : G.Adj x c) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    IsMinor (⊤ : SimpleGraph (Fin 4)) G := by sorry
