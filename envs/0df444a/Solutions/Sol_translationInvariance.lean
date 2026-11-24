-- Prove2me | solution 1 for translationInvariance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:11:16.857378+00:00
-- url     : https://prove2.me/submissions/4999b017-a345-49f0-a23a-80982eedf8e6

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Definitions.Def_FriezePatterns_chapter1
import Theorems.Thm_glideSymm

set_option autoImplicit true

theorem _root_.solution (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀m, f (i,m) = f (i,m+n+1) := by
  intro i ileq m
  have key := glideSymm F f n i ileq m
  have key2 := glideSymm F f n (n+1-i) (Nat.sub_le (n+1) i) (m+i)
  simp [Nat.sub_sub_eq_min, ileq, add_assoc] at key2
  rw [←key, ←key2, add_assoc]
