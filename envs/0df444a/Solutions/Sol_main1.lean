-- Prove2me | solution 1 for main1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:17:48.394883+00:00
-- url     : https://prove2.me/submissions/04afc765-2d9c-465d-8ec4-d86bbeaf43e6

import Definitions.Def_FriezePatterns_chapter1
import Definitions.Def_FriezePatterns_chapter2
import Definitions.Def_FriezePatterns_chapter3
import Theorems.Thm_FluteBounded


set_option autoImplicit true

theorem _root_.solution (n : ℕ) (h : n ≠ 0) : ∀ (f : ℕ × ℕ → ℚ) (_ : arith_fp f n), ∀ (a : ℕ × ℕ), f a ≤ Nat.fib n := by
  intro f hf ⟨i,m⟩
  by_cases hn : n=1
  simp [hn, Nat.fib_one]
  match i with
  | 0 => simp [hn, hf.topBordZeros m]
  | 1 => simp [hn, hf.topBordOnes m]
  | i+2 => simp [hn, hf.botBordZeros_n (i+2) m (by omega)]
  have hn' : n > 1 := by omega
  let g := @friezeToFlute f n m (by omega) hf
  by_cases hi₀ : i = 0
  simp [hi₀, hf.topBordZeros m]
  by_cases hi₁ : i = 1
  simp [hi₁, hf.topBordOnes m]
  have hn'' : n >0 := by omega
  have : Nat.fib n > 0 := Nat.fib_pos.mpr hn''
  linarith
  by_cases hi₂ : i ≥ n+1
  simp [hi₂, hf.botBordZeros_n i m hi₂]
  by_cases hi₃ : i = n
  simp [hi₃, hf.botBordOnes_n m]
  have hi₄ : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
  linarith
  have key := FluteBounded n (by omega) g (i-1) (by omega)
  have hg : g.a = flute_f f n m := rfl ; rw [hg] at key ; unfold flute_f at key ; simp at key
  have hi₆ : (i-1)%(n-1)+1 = i := by rw [Nat.mod_eq_of_lt (by omega)] ; omega
  rw [hi₆] at key
  have hpos : 0 ≤ (f (i, m)).num := le_of_lt (Rat.num_pos.mpr (hf.positive i m (by omega) (by omega)))
  have hfm : f (i, m) = ((f (i, m)).num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den (f (i, m)), hf.integral i m]
    simp
  rw [hfm]
  have hnum : (f (i, m)).num ≤ (Nat.fib n : ℤ) := by omega
  exact_mod_cast hnum
