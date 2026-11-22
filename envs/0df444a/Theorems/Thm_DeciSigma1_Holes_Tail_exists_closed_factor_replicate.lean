-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_closed_factor_replicate
-- name    : DeciSigma1.Holes.Tail.exists_closed_factor_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:45.337275+00:00
-- url     : https://prove2.me/theorems/f19e67c7-36c8-461c-909c-47aaee972640
-- title:
--   Tail: exists closed factor replicate
-- statement:
--   Closed factors free of suffix occurrences of at most `m` targets with a common chain budget
--   for the chains that start at the initial window `bs` or later, closed for the suffix dictionary
--   of the targets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L299-L311
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L299-L311

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S]
variable (T : Readers.Table α S k) (q0 : S) (x : List α)

theorem DeciSigma1.Holes.Tail.exists_closed_factor_replicate (ts : List (List α)) {m Sb bs : ℕ} (hm : ts.length ≤ m)
    (hS : ∀ t ∈ ts, ChainBoundFrom t bs Sb) {u : ℕ}
    (hseg : u + suffixLengthBound m (Fintype.card S) (List.replicate m Sb) bs ≤ x.length) :
    ∃ B c c', bs ≤ B ∧ B ≤ suffixLengthEnvelope m (Fintype.card S) (List.replicate m Sb) bs ∧
      u ≤ c ∧ c' ≤ u + suffixLengthBound m (Fintype.card S) (List.replicate m Sb) bs ∧
      NodeClosedAt T q0 (suffixDictionary ts B) x c c' ∧
      (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween x t B c c') ∧ B < c' - c ∧
      c' - c ≤ factorLengthBound m (Fintype.card S) B := by sorry
