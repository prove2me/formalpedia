-- Prove2me | solution 1 for davenport_constant_sharp
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:47:19.959975+00:00
-- url     : https://prove2.me/submissions/bce616b3-6134-4806-a1b0-6cb9e4e530e8

import Mathlib

/-!
**Sharpness of Davenport's theorem.** The sequence of `n - 1` ones in `ZMod n` has no
nonempty zero-sum subsequence, so the Davenport constant of the cyclic group `ZMod n` is
exactly `n`: `davenport_zero_sum` gives the upper bound `D(C_n) ≤ n`, and this example
rules out any improvement.
-/

open Finset

/-- The Davenport constant of `ZMod n` is at least `n`: `n - 1` ones have no
nonempty zero-sum subsequence. -/
theorem solution (n : ℕ) (hn : 0 < n) :
    ¬ ∃ t : Finset ℕ, t.Nonempty ∧ t ⊆ Finset.range (n - 1) ∧ ∑ k ∈ t, (1 : ZMod n) = 0 := by
  rintro ⟨t, htne, htsub, htsum⟩
  -- the sum is `t.card • 1 = ↑t.card` in `ZMod n`, which vanishes iff `n ∣ t.card`
  have hcard : ∑ k ∈ t, (1 : ZMod n) = ((t.card : ℕ) : ZMod n) := by
    simp [Finset.sum_const]
  rw [hcard] at htsum
  have hdvd : n ∣ t.card := (ZMod.natCast_eq_zero_iff t.card n).mp htsum
  have hle : t.card ≤ n - 1 := by
    have h1 := Finset.card_le_card htsub
    rw [Finset.card_range] at h1
    exact h1
  have hpos : 1 ≤ t.card := Finset.card_pos.2 htne
  obtain ⟨c, hc⟩ := hdvd
  rcases c.eq_zero_or_pos with rfl | hc0
  · simp only [Nat.mul_zero] at hc
    rw [hc] at hpos
    exact absurd hpos (by omega)
  · have hbig : n ≤ t.card := by
      have h1 : n * 1 ≤ n * c := Nat.mul_le_mul le_rfl hc0
      rw [mul_one] at h1
      rw [hc]
      exact h1
    exact absurd (hbig.trans hle) (by omega)
