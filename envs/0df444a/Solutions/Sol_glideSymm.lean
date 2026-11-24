-- Prove2me | solution 1 for glideSymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:18.546257+00:00
-- url     : https://prove2.me/submissions/e0e95aef-1e0b-48b9-9424-e25a1244dc7b

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Definitions.Def_FriezePatterns_chapter1
import Theorems.Thm_pattern_nContinuant1
import Theorems.Thm_pattern_nContinuant2

set_option autoImplicit true

theorem _root_.solution (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀ m, f (n+1-i, m+i) = f (i,m) := by
-- we need glideSymm in chapter 3
  intro i ileq
  induction' i using Nat.twoStepInduction with i ih₁ ih₂
  simp
  intro m
  rw [@pattern_n.botBordZeros_n F _ f n _ (n+1) m (by linarith), @pattern_n.topBordZeros F _ f n _ m]
  simp at *
  intro m
  rw [@pattern_n.botBordOnes_n F _ f n _ (m+1), @pattern_n.topBordOnes F _ f n _ m]
  simp at *
  intro m
  rw [Nat.sub_add_eq, ← add_assoc m i 2]
  have h₁ : i ≤ n-1 := by omega
  have h₂ : f (2,m+i) = f (n-1,m+i+2) := by -- we first prove P₂
    have key := pattern_nContinuant2 F f n 0 (by linarith) (m+i)
    simp [@pattern_n.topBordZeros F _ f n _ (m+i+2), @pattern_n.topBordOnes F _ f n _ (m+i+1)] at key
    exact (sub_eq_zero.mp key.symm).symm
  have h₃ : f (i+1,m) = f (n-i,m+i+1) := by
    have := ih₂ (by linarith) m
    simpa [add_assoc] using this.symm
  have h₄ : f (i,m) = f (n+1-i,m+i) := by
    have := ih₁ (by linarith) m
    simpa using this.symm
  have h₅ : f (n-i-1,m+i+2) = f (n-1,m+i+2) * f (n-i,m+i+1) - f (n+1-i,m+i) := by
    have key := pattern_nContinuant2 F f n (n-i-1) (by omega) (m+i)
    rw [key]
    congr <;> omega
  symm
  calc
    f (i+2,m) = f (2,m+i) * f (i+1,m) - f (i,m) := by rw [pattern_nContinuant1 F f n i h₁ m]
              _ = f (n-1,m+i+2) * f (n-i,m+i+1) - f (n+1-i,m+i) := by congr
              _ = f (n-i-1,m+i+2) := by rw [h₅]
