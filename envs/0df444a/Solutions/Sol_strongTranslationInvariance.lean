-- Prove2me | solution 1 for strongTranslationInvariance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:12:04.634496+00:00
-- url     : https://prove2.me/submissions/b56a6f20-bca1-4a7d-9d96-0593b1206bee

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Definitions.Def_FriezePatterns_chapter1
import Theorems.Thm_translationInvariance

set_option autoImplicit true

theorem _root_.solution (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n+1 → ∀m, f (i,m) = f (i,m%(n+1)) := by
  intro i ileq m
  induction' m using Nat.strong_induction_on with m ih
  by_cases hm : m < n+1
  rw [Nat.mod_eq_of_lt hm]
  simp at hm
  have h₁ : m ≥ (n+1) := by omega
  have h₂ : m - (n+1) < m := by omega
  have key : f (i, m - (n + 1)) = f (i, m) := by
    calc f (i,m - (n+1)) = f (i, m - (n+1) + (n+1)) := translationInvariance F f n i (by linarith) (m - (n + 1))
    _= f (i,m) := by congr ; omega
  rw [← key]
  specialize ih (m - (n+1)) h₂
  have h₃ : m % (n + 1) = (m - (n + 1)) % (n + 1) := by apply Nat.mod_eq_sub_mod h₁
  rw [h₃, ih]
