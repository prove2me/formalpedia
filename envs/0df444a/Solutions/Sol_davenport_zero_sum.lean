-- Prove2me | solution 1 for davenport_zero_sum
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T08:23:36.073956+00:00
-- url     : https://prove2.me/submissions/be69d770-dba5-4df2-8b88-5c1760c3fbdb

import Mathlib

/-!
**Davenport's theorem**: every sequence of `n` elements of `ZMod n` has a nonempty
subsequence whose sum is zero — the upper-bound half of "the Davenport constant of the
cyclic group `ZMod n` is `n`".

The proof is the one-line partial-sums argument: the `n + 1` initial sums
`p k = a 0 + ⋯ + a (k-1)` for `0 ≤ k ≤ n` live in a group of `n` elements, so two of them
coincide by the pigeonhole principle, and their difference is the sum over the intervening
nonempty interval of indices. The bound is sharp: the sequence `1, 1, …, 1` of length
`n - 1` has no nonempty zero-sum subsequence, since `k • (1 : ZMod n) = 0` only at
`k = 0` and `k = n`.
-/

open Finset

/-- **Davenport's theorem**: `n` elements of `ZMod n` contain a nonempty zero-sum subsequence. -/
theorem solution (n : ℕ) (hn : 0 < n) (a : ℕ → ZMod n) :
    ∃ t : Finset ℕ, t.Nonempty ∧ t ⊆ Finset.range n ∧ ∑ k ∈ t, a k = 0 := by
  haveI : NeZero n := neZero_iff.2 hn.ne'
  -- the initial sums, as a function of the number of terms taken
  set p : ℕ → ZMod n := fun k => ∑ i ∈ Finset.range k, a i with hp
  -- pigeonhole: `p` cannot be injective on the `n + 1` indices `0, …, n`
  obtain ⟨i, j, hij, hpij⟩ : ∃ i j : Fin (n + 1), i ≠ j ∧ p i.val = p j.val := by
    by_contra hcon
    push_neg at hcon
    have h1 := Fintype.card_le_of_injective (fun k : Fin (n + 1) => p k.val)
      (fun k k' h => by
        by_contra hne
        exact hcon k k' hne h)
    rw [Fintype.card_fin (n + 1), ZMod.card] at h1
    omega
  -- the intervening interval of indices works; order `i` and `j` first
  have key : ∀ i j : ℕ, i < j → j ≤ n → p i = p j →
      ∃ t : Finset ℕ, t.Nonempty ∧ t ⊆ Finset.range n ∧ ∑ k ∈ t, a k = 0 := by
    intro i j hij hjn hpij
    refine ⟨Finset.Ico i j, ⟨i, Finset.mem_Ico.2 ⟨le_rfl, hij⟩⟩, ?_, ?_⟩
    · intro k hk
      exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_Ico.1 hk).2 hjn)
    · -- decompose `range j = range i ∪ Ico i j` (disjoint), so the interval sum is the difference
      have hun : Finset.range i ∪ Finset.Ico i j = Finset.range j := by
        ext k
        simp only [mem_union, mem_range, mem_Ico]
        omega
      have hdis : Disjoint (Finset.range i) (Finset.Ico i j) := by
        rw [Finset.disjoint_right]
        intro k hk
        rw [mem_Ico] at hk
        rw [mem_range]
        omega
      have hsplit : ∑ k ∈ Finset.range j, a k = ∑ k ∈ Finset.range i, a k
          + ∑ k ∈ Finset.Ico i j, a k := by
        rw [← hun, Finset.sum_union hdis]
      simp only [hp] at hsplit hpij ⊢
      rw [← hpij] at hsplit
      simpa using hsplit.symm
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact key i.val j.val h (by omega) hpij
  · exact absurd (Fin.ext h) hij
  · exact key j.val i.val h (by omega) hpij.symm
