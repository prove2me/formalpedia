-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_initialSegment_transversal
-- name    : DeciSigma1.Holes.Tail.exists_initialSegment_transversal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:25.272741+00:00
-- url     : https://prove2.me/theorems/8b0db08a-bea1-4939-a233-eec92a4d0352
-- title:
--   Tail: exists initial Segment transversal
-- statement:
--   If `f` takes at least `K` values on `Fin n`, some initial segment `{i | i < m}` has exactly
--   `K` values, and they are taken injectively on a set `R` of `K` indices of the segment.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L92-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L92-L119

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.exists_initialSegment_transversal {β : Type*} [DecidableEq β] {n K : ℕ} (f : Fin n → β)
    (hK : K ≤ (Finset.univ.image f).card) :
    ∃ (m : ℕ) (R : Finset (Fin n)), (∀ i ∈ R, i.val < m) ∧ Set.InjOn f R ∧ R.card = K ∧
      ((Finset.univ.filter fun i : Fin n => i.val < m).image f).card = K := by sorry
