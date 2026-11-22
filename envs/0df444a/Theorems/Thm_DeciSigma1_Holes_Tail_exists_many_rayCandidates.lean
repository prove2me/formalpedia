-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_many_rayCandidates
-- name    : DeciSigma1.Holes.Tail.exists_many_rayCandidates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:27.911971+00:00
-- url     : https://prove2.me/theorems/da45649a-920d-4911-baaa-2bdde4ba1c5a
-- title:
--   Tail: exists many ray Candidates
-- statement:
--   A word whose rejected tail has no periodic cover at level `l` has candidates, one closed
--   factor in each segment of `escapeLengthBound l` cuts after the first rejected cut, free of the
--   suffixes of every target whose chains from `startWindow l` on have at most `Q + N` steps, where
--   `Q = pieceCountBase`. At least `Q - 1` of the candidates have pairwise distinct onsets after the
--   first rejected cut. All of them are among the first `Q + 2` distinct onsets, so for each the
--   tail before its factor is covered by at most `Q + 2` factors of period at most `periodBound l`
--   and at most `(Q + 3) (3 · escapeLengthBound l + 3)` other letters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L170-L298
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L170-L298

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
variable [DecidableEq α] [Fintype α] [Fintype S] [DecidableEq S]
omit [DecidableEq S]

theorem DeciSigma1.Holes.Tail.exists_many_rayCandidates (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} {v : Fin k} (hv : M.Eligible W v) {l : ℕ}
        (hM : ¬ CoordinateCover C l M W v)
    (ts : List (List α)) (hts : ts.length ≤ k)
        (hS : ∀ t ∈ ts, ChainBoundFrom t (C.startWindow l) (C.pieceCountBase + Fintype.card S)) :
    ∃ (n : ℕ) (cand : Fin n → RayCandidate M W ts v) (R : Finset (Fin n)),
      (∀ r, C.startWindow l ≤ (cand r).windowLength ∧ M.firstRejection W v ≤ (cand r).startCut ∧
        (cand r).endCut - (cand r).startCut ≤ C.periodBound l ∧ ∀ t ∈ ts,
            NoSuffixOccurrenceEndsBetween (W v) t (cand r).windowLength (cand r).startCut
                (cand r).endCut) ∧
      Set.InjOn (fun r => (cand r).ray.onset) R ∧
          (∀ r ∈ R, M.firstRejection W v < (cand r).ray.onset) ∧
      C.pieceCountBase - 1 ≤ R.card ∧
      ∀ r ∈
          R, PeriodicCover ((W v).take (cand r).startCut) (M.firstRejection W v)
              (C.pieceCountBase + 2) (C.periodBound l)
        ((C.pieceCountBase + 3) * (3 * C.escapeLengthBound l + 3)) := by sorry
