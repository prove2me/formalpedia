-- Prove2me | Theorems.Thm_EulerPetersen_eulerian_orientation
-- name    : EulerPetersen.eulerian_orientation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:53:12.028287+00:00
-- url     : https://prove2.me/theorems/777ae767-6b5b-4f4b-b5ec-e83138194fbc
-- title:
--   Euler Petersen: eulerian orientation
-- statement:
--   The Euler Petersen construction uses the eulerian orientation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Solution.lean#L46-L50
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Solution.lean#L46-L50

module
public import Definitions.Def_Euler
public import Definitions.Def_EulerPetersen_Solution
set_option autoImplicit true
@[expose] public section
public section
open EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem EulerPetersen.eulerian_orientation (heven : ∀ v, Even (G.degree v)) :
    ∃ Ds : Finset G.Dart, (∀ d ∈ Ds, ∀ d' ∈ Ds, d.edge = d'.edge → d = d') ∧
      (∀ v, (Ds.filter fun d => d.fst = v).card = (Ds.filter fun d => d.snd = v).card) ∧
      ∀ e ∈ G.edgeSet, ∃ d ∈ Ds, d.edge = e := by sorry
