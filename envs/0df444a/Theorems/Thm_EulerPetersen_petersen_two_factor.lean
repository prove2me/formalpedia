-- Prove2me | Theorems.Thm_EulerPetersen_petersen_two_factor
-- name    : EulerPetersen.petersen_two_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:20:06.736384+00:00
-- url     : https://prove2.me/theorems/3384d6b1-4fe2-4172-af4f-fbd94b7db710
-- title:
--   Euler Petersen: petersen two factor
-- statement:
--   The Euler Petersen construction uses the petersen two factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Solution.lean#L52-L56
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Solution.lean#L52-L56

module
public import Definitions.Def_Euler
public import Definitions.Def_EulerPetersen_Solution
public import Theorems.Thm_SimpleGraph_petersen_two_factor

set_option autoImplicit true
@[expose] public section
public section
open EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem EulerPetersen.petersen_two_factor (k : ℕ) (h : ∀ v, G.degree v = 2 * k) :
    ∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G) ∧
      (∀ i v, ((F i).neighborSet v).ncard = 2) ∧
      (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ ⨆ i, F i = G := by sorry
