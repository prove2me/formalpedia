-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_RayCandidate_onset_le
-- name    : DeciSigma1.Holes.Tail.RayCandidate.onset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:46.440576+00:00
-- url     : https://prove2.me/theorems/64fa5a85-968e-4a0e-b758-ff871520ef53
-- title:
--   Ray Candidate: onset le
-- statement:
--   The Ray Candidate construction uses the onset le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L80-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L80-L81

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

theorem DeciSigma1.Holes.Tail.RayCandidate.onset_le (x : RayCandidate M W ts v) : x.ray.onset ≤ x.startCut := by sorry
