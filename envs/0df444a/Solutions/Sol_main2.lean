-- Prove2me | solution 1 for main2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:18:00.045741+00:00
-- url     : https://prove2.me/submissions/1f1cf5c5-a3b0-4511-90cb-c8f8ddef91e9

import Definitions.Def_FriezePatterns_chapter1
import Definitions.Def_FriezePatterns_chapter2
import Definitions.Def_FriezePatterns_chapter3

set_option autoImplicit true

theorem _root_.solution (n : ℕ) (hn : n ≠ 0) : ∃ (f : ℕ × ℕ → ℚ) (hf : arith_fp f n), ∃ (a : ℕ × ℕ), f a = Nat.fib n := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  -- even case
  · have : k > 0 := by
      by_contra!
      simp [hk] at this; rw [this] at hk; simp at hk; omega
    have : k ≠ 0 := by omega
    let j := k-1
    have hj : n = 2*j+2 := by omega
    use frieze_f (fib_flute_even j)
    let temp := fluteToFrieze (fib_flute_even j) (by omega)
    conv at temp =>
      rhs
      rw [←hj]
    use temp
    have h₁ : ∃ (w : ℕ × ℕ), frieze_f (fib_flute_even j) w = Nat.fib (2*j+2) := by
      use (j+1, 0)
      have h₃: ¬2 * j + 2 ≤ j := by omega
      simp [frieze_f,h₃]
      unfold fib_flute_even
      by_cases h₂ : j = 0
      simp [h₂]
      unfold a_even; simp [h₂,hj]
      -- j ≠ 0
      simp [h₂]
      have h₄ : ¬ j ≥ 2*j +1 := by omega
      --have h₅ : 1 + 4 * j - 2 * j = 2*j + 2 := by omega
      unfold a_even; simp [h₂,hj,h₄]
    choose w hw using h₁
    use w
    rw [hj]
    assumption
  -- odd case
  · use frieze_f (fib_flute_odd k)
    let temp := fluteToFrieze (fib_flute_odd k) (by omega)
    conv at temp =>
      rhs
      rw [←hk ]
    use temp
    have h₁ : ∃ (w : ℕ × ℕ), frieze_f (fib_flute_odd k) w = Nat.fib (2*k+1) := by
      use (k+1, 0)
      --have h₂ : ¬ k = 0 := by omega
      have h₃: ¬2 * k + 1 ≤ k := by omega
      simp [frieze_f,h₃]
      unfold fib_flute_odd
      by_cases h₂ : k = 0
      simp [h₂]
      unfold a_odd; simp [h₂,hk]
      -- k ≠ 0
      simp [h₂]
      have h₄ : ¬ 2*k ≤ k := by omega
      have h₅ : 1 + 4 * k - 2 * k = 2*k + 1 := by omega
      unfold a_odd; simp [h₂,hk,h₄,h₅]
    choose w hw using h₁
    use w
    rw [hk]
    assumption
