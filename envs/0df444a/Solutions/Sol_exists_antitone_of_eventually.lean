-- Prove2me | solution 1 for exists_antitone_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:29:35.242194+00:00
-- url     : https://prove2.me/submissions/0f83916a-02a7-4f78-a35c-4eb7e2658143

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open Filter Set

theorem solution {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  rw [eventually_atTop] at hu
  obtain ⟨N, hN⟩ := hu
  refine ⟨fun n => u (max n N), ?_, ?_, ?_⟩
  · rintro x ⟨n, rfl⟩
    exact ⟨max n N, rfl⟩
  · apply antitone_nat_of_succ_le
    intro n
    by_cases hn : n < N
    · rw [max_eq_right (Nat.succ_le_of_lt hn), max_eq_right hn.le]
    · have hn' : N ≤ n := Nat.le_of_not_gt hn
      rw [max_eq_left (hn'.trans (Nat.le_succ n)), max_eq_left hn']
      exact hN n hn'
  · filter_upwards [eventually_ge_atTop N] with n hn
    rw [max_eq_left hn]
