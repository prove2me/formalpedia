-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_RayCandidate_period_le
-- name    : DeciSigma1.Holes.Tail.RayCandidate.period_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:18.268976+00:00
-- url     : https://prove2.me/theorems/61a96435-9993-4a01-bbc6-19be998edb11
-- title:
--   Ray Candidate: period le
-- statement:
--   The Ray Candidate construction uses the period le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L83-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L83-L84

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
open DeciSigma1.Holes.Tail.RayCandidate
variable [DecidableEq α] {M : StructuralReader α S k} {W : Fin k → List α} {ts : List (List α)}
  {v : Fin k}

theorem DeciSigma1.Holes.Tail.RayCandidate.period_le (x : RayCandidate M W ts v) : x.ray.period ≤ x.endCut - x.startCut := by sorry
