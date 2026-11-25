-- Prove2me | Theorems.Thm_EulerPetersen_eulerian_trail_iff
-- name    : EulerPetersen.eulerian_trail_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:52:19.159336+00:00
-- url     : https://prove2.me/theorems/f14ba425-3b94-522e-a387-442d84e6cb6a
-- title:
--   Euler Petersen: eulerian trail iff
-- statement:
--   The Euler Petersen construction uses the eulerian trail iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Solution.lean#L37-L40
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Solution.lean#L37-L40

module
public import Definitions.Def_Euler
public import Definitions.Def_EulerPetersen_Solution
set_option autoImplicit true
@[expose] public section
public section
open EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem EulerPetersen.eulerian_trail_iff (hconn : G.Connected) :
    (∃ u v, ∃ p : G.Walk u v, p.IsEulerian) ↔
      Fintype.card {v | Odd (G.degree v)} = 0 ∨ Fintype.card {v | Odd (G.degree v)} = 2 := by sorry
