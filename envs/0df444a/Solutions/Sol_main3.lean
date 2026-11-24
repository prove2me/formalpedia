-- Prove2me | solution 1 for main3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:23:32.531229+00:00
-- url     : https://prove2.me/submissions/4e559761-17b2-45a6-b9f6-647329d8b7f3

import Definitions.Def_FriezePatterns_chapter1
import Definitions.Def_FriezePatterns_chapter2
import Definitions.Def_FriezePatterns_chapter3
import Theorems.Thm_main1
import Theorems.Thm_main2

set_option autoImplicit true

theorem _root_.solution (n : ℕ) (hn: n≠ 0) : ∃ (g : ℕ × ℕ → ℚ) (_ : arith_fp g n), ∃ (b : ℕ × ℕ ), (∀ (f : ℕ × ℕ → ℚ) (_ : arith_fp f n), ∀ (a : ℕ × ℕ),
(f a ≥ g b → f a = g b)) ∧ g b = Nat.fib n := by
  have h : ∃ (g : ℕ × ℕ → ℚ) (_ : arith_fp g n), ∃ (b : ℕ × ℕ), g b = Nat.fib n := main2 n hn
  choose g hg b hb using h
  use g; use hg; use b
  constructor
  · intro f hf ⟨i,m⟩
    have h : f (i,m) ≤ g b := by
      calc f (i,m) ≤ Nat.fib n := main1 n hn f hf (i,m)
      _ = g b := by rw [hb]
    intro h'
    linarith
  · exact hb
