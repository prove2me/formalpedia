-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_ncInv_walk
-- name    : DeciSigma1.Holes.Tail.ncInv_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:41.916799+00:00
-- url     : https://prove2.me/theorems/c5e914be-451e-46a1-a36b-0a4686ca2ba5
-- title:
--   Tail: nc Inv walk
-- statement:
--   The Tail construction uses the nc Inv walk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L271-L299
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L271-L299

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]
variable {ι : Type} [Fintype S]
variable [Fintype ι] [DecidableEq ι] (M : StructuralReader α S k) (st : ι → S) (Ω : ι → Ray α)
  (J : ι → ℕ) (v : ι)
variable {M st Ω J v}

theorem DeciSigma1.Holes.Tail.ncInv_walk (hclean : ∀ u, u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u)) :
    ∀ (ys : List ι) (y : ι), (raySystem M st Ω J).IsWalk (ys ++ [y]) → CandidateInvariant Ω J v y →
      ∀ z ∈ ys, CandidateInvariant Ω J v z ∧ z ≠ v
  := by sorry
