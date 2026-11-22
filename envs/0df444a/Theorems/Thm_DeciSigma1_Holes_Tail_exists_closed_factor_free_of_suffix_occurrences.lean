-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_closed_factor_free_of_suffix_occurrences
-- name    : DeciSigma1.Holes.Tail.exists_closed_factor_free_of_suffix_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:39.205635+00:00
-- url     : https://prove2.me/theorems/ca538ba7-3681-460e-b20b-d2e6c5a7c3e2
-- title:
--   Tail: exists closed factor free of suffix occurrences
-- statement:
--   Let `ds` be a list of at most `m` words. If the chains of the targets `ts` that start at a
--   length at least `b₀` have at most the budgets `Ss`, then for every `bs ≥ b₀` any
--   `suffixLengthBound m N Ss bs` consecutive cuts `u, u + 1, …` of `x` contain cuts `c < c'` that are
--   closed for the suffix dictionary of `ds` at a window `B` with
--   `bs ≤ B ≤ suffixLengthEnvelope m N Ss bs`, such that no occurrence of the suffix of length `B` of
--   any target ends in `(c, c']`, and `B < c' - c ≤ factorLengthBound m N B`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L174-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean#L174-L271

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

theorem DeciSigma1.Holes.Tail.exists_closed_factor_free_of_suffix_occurrences (ds : List (List α)) {m : ℕ}
    (hm : ds.length ≤ m) (b₀ : ℕ) :
    ∀ (ts : List (List α)) (Ss : List ℕ), List.Forall₂ (fun t S => ChainBoundFrom t b₀ S) ts Ss →
    ∀ bs u, b₀ ≤ bs → u + suffixLengthBound m (Fintype.card S) Ss bs ≤ x.length + 1 →
      ∃ B c c', bs ≤ B ∧ B ≤ suffixLengthEnvelope m (Fintype.card S) Ss bs ∧ u ≤ c ∧
        c' < u + suffixLengthBound m (Fintype.card S) Ss bs ∧
            NodeClosedAt T q0 (suffixDictionary ds B) x c c' ∧
        (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween x t B c c') ∧ B < c' - c ∧
          c' - c ≤ factorLengthBound m (Fintype.card S) B := by sorry
