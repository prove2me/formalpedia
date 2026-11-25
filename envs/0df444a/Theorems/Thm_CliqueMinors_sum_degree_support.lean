-- Prove2me | Theorems.Thm_CliqueMinors_sum_degree_support
-- name    : CliqueMinors.sum_degree_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:40:06.12264+00:00
-- url     : https://prove2.me/theorems/fb49b72f-2883-41ae-9c80-e5a312f33c46
-- title:
--   Clique Minors: sum degree support
-- statement:
--   The Clique Minors construction uses the sum degree support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L45-L50
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L45-L50

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

theorem CliqueMinors.sum_degree_support {G : SimpleGraph V} {S : Finset V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    ∑ v ∈ S, G.degree v = 2 * G.edgeFinset.card := by sorry
