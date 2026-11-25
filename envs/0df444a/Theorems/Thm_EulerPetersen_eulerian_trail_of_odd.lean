-- Prove2me | Theorems.Thm_EulerPetersen_eulerian_trail_of_odd
-- name    : EulerPetersen.eulerian_trail_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:52:30.30086+00:00
-- url     : https://prove2.me/theorems/0b4d3c62-a8b4-54e2-b549-e48aa19a24d8
-- title:
--   Euler Petersen: eulerian trail of odd
-- statement:
--   The Euler Petersen construction uses the eulerian trail of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Solution.lean#L42-L44
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Solution.lean#L42-L44

module
public import Definitions.Def_Euler
public import Definitions.Def_EulerPetersen_Solution
set_option autoImplicit true
@[expose] public section
public section
open EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem EulerPetersen.eulerian_trail_of_odd (hconn : G.Connected) {a b : V} (hab : a ≠ b)
    (hodd : ∀ x, Odd (G.degree x) ↔ x = a ∨ x = b) : ∃ p : G.Walk a b, p.IsEulerian := by sorry
