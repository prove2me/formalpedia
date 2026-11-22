-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_rayCandidate_no_selfAdmission
-- name    : DeciSigma1.Holes.Tail.rayCandidate_no_selfAdmission
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:32.651019+00:00
-- url     : https://prove2.me/theorems/cce5fb7a-bf10-49ec-8d4e-2ee2d1a2c9fa
-- title:
--   Tail: ray Candidate no self Admission
-- statement:
--   The ray of a candidate has no admitted comparison with itself beyond those of the original
--   word: a comparison with `a ≤ b ≤ J` and equal infinite suffixes forces `a = b`, and the pair at
--   equal cuts is a pair of the original hole.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L419-L436
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L419-L436

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

theorem DeciSigma1.Holes.Tail.rayCandidate_no_selfAdmission [DecidableEq α] [DecidableEq S] {M : StructuralReader α S k}
    {W : Fin k → List α}
    (hW : M.IsHole W) {i : Fin k} {Ω : Ray α} {E : ℕ} (hag : RayAgrees Ω (W i) E)
    (hJE : M.firstRejection W i ≤ E) (hJA : M.firstRejection W i < Ω.onset) :
    ∀ a b, b ≤ M.firstRejection W i → a ≤ b →
      M.admitted (rayState M (M.start i) Ω a) (rayState M (M.start i) Ω b) = true →
      ¬ ∀ t, Ω.stream (a + t) = Ω.stream (b + t) := by sorry
