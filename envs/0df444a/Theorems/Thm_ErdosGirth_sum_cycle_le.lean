-- Prove2me | Theorems.Thm_ErdosGirth_sum_cycle_le
-- name    : ErdosGirth.sum_cycle_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:19.614739+00:00
-- url     : https://prove2.me/theorems/270bdb3c-016a-562c-aa64-ead3f37cacb1
-- title:
--   Erdos Girth: sum cycle le
-- statement:
--   The Erdos Girth construction uses the sum cycle le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L142-L167
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L142-L167

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical

theorem ErdosGirth.sum_cycle_le {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (ℓ : ℕ) :
    ∑ u : Fin m, ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
      (if c.IsCycle then p ^ ℓ else 0) ≤ ((m : ℝ) * p) ^ ℓ := by sorry
