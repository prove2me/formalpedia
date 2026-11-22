-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_compatible_rayCandidate
-- name    : DeciSigma1.Holes.Tail.exists_compatible_rayCandidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:32.648862+00:00
-- url     : https://prove2.me/theorems/983f763a-a4f1-4b79-867d-6bf5c0b2a012
-- title:
--   Tail: exists compatible ray Candidate
-- statement:
--   Given the rays `U` chosen before the word `v`, each agreeing with its original word and with
--   a bounded period if it is periodic at its first rejected cut, some candidate of `v` with onset
--   after the first rejected cut has no forbidden overlap with any of them: each earlier ray
--   excludes at most `2 (N - 1)` candidates, and there are at least `Q - 1 > 2 (k - 1) (N - 1)`
--   candidates, where `Q = pieceCountBase`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L305-L410
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L305-L410

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

theorem DeciSigma1.Holes.Tail.exists_compatible_rayCandidate (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} (hW : M.IsHole W) {v : Fin k} {l : ℕ} (hl : 1 ≤ l)
    (hM : ¬ CoordinateCover C l M W v) (ts : List (List α)) (hts : ts.length ≤ k)
    (hS : ∀ t ∈ ts, ChainBoundFrom t (C.startWindow l) (C.pieceCountBase + Fintype.card S))
    (U : Finset (Fin k)) (hvU : v ∉ U)
    (Ωu : Fin k → Ray α) (Eu : Fin k → ℕ)
    (hU : ∀ u ∈ U, RayAgrees (Ωu u) (W u) (Eu u) ∧ (Ωu u).onset ≤ Eu u ∧
      M.firstRejection W u ≤ Eu u ∧ ((Ωu u).onset ≤ M.firstRejection W u →
          (Ωu u).period ≤ C.periodBound (l - 1))) :
    ∃ x : RayCandidate M W ts v, C.startWindow l ≤ x.windowLength ∧
        M.firstRejection W v ≤ x.startCut ∧
        x.endCut - x.startCut ≤ C.periodBound l ∧
      (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween (W v) t x.windowLength x.startCut x.endCut) ∧
          M.firstRejection W v <
          x.ray.onset ∧
      PeriodicCover ((W v).take x.startCut) (M.firstRejection W v) (C.pieceCountBase + 2)
          (C.periodBound l)
        ((C.pieceCountBase + 3) * (3 * C.escapeLengthBound l + 3)) ∧
      ∀ u ∈
          U, NoForbiddenRayOverlap x.ray (Ωu u) (M.firstRejection W v) (M.firstRejection W u) := by sorry
