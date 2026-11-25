-- Prove2me | Theorems.Thm_CliqueMinors_degree_eq_zero_of_not_mem_support
-- name    : CliqueMinors.degree_eq_zero_of_not_mem_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:41:27.275346+00:00
-- url     : https://prove2.me/theorems/275a6b45-e6ef-52b5-90c6-36e6187f6f06
-- title:
--   Clique Minors: degree eq zero of not mem support
-- statement:
--   The Clique Minors construction uses the degree eq zero of not mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L39-L43
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L39-L43

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

theorem CliqueMinors.degree_eq_zero_of_not_mem_support {G : SimpleGraph V} {S : Finset V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) {v : V} (hv : v ∉ S) : G.degree v = 0 := by sorry
