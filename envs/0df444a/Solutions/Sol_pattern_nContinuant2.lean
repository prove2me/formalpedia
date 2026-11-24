-- Prove2me | solution 1 for pattern_nContinuant2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:09:23.263118+00:00
-- url     : https://prove2.me/submissions/83c92390-f1d1-44ca-8c65-c60c9d89bdf2

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Definitions.Def_FriezePatterns_chapter1

set_option autoImplicit true

theorem _root_.solution (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n-1 → ∀m, f (i,m+2) = f (n-1,m+2)*f (i+1,m+1) - f (i+2,m) := by
  by_cases one_leq_n : 1 ≤ n
  suffices pattern_nContinuant2flipped : ∀ i, i ≤ n-1 → ∀m, f (n-i-1,m+2) = f (n-1,m+2)*f (n-i,m+1) - f (n-i+1,m)
  -- Flip i to n-i so we can induct forwards
  ·intro i h m
   have key : n - i - 1 ≤ n - 1 := by omega
   have i_plus_one_leq_n : i + 1 ≤ n := by omega
   have key2 : n - (n - i - 1) - 1 = i := by omega
   have key3 : n - (n - i - 1) = i + 1 := by omega

   calc f (i, m + 2) = f (n - (n - i - 1) - 1, m + 2) := by rw[key2]
            _= f (n-1,m+2)*f (n-(n - i - 1),m+1) - f (n-(n - i - 1) + 1,m) := by rw[pattern_nContinuant2flipped (n - i - 1) key]
            _= f (n-1,m+2)*f (i+1,m+1) - f (i+2,m) := by rw[key3]

  -- Have proved sufficiency of the flipped version

  ·intro i h
   induction i with
   | zero =>
   intro m
   simp
   have hₙ : f (n,m+1) = 1 ∧ f (n+1,m) = 0 := by exact ⟨pattern_n.botBordOnes_n (m+1), @pattern_n.botBordZeros_n F _ f n _ (n+1) m (by linarith)⟩
   rw[hₙ.2,hₙ.1,sub_zero,mul_one]
   | succ k ih =>
   intro m

   have a₀₁ : 1 ≤ n - k - 1 := by omega
   have a₀₁' : 2 ≤ n - k := by omega
   have a₁ : n - (k + 1) - 1 + 2 = n - k := by omega
   have a₂ : n - (k + 1) - 1 + 1 = n - k - 1 := by omega
   have a₃ : 1 ≤ n - (k + 1) - 1 + 2 ∧ n - (k + 1) - 1 + 2 ≤ n := by omega
   have a₅ : k ≤ n-1 := by omega
   have a₇ : n - (k + 1) - 1 ≤ n - 1 := by omega
   have a₁₁ : n - (k + 1) - 1 + 1 = n - (k + 1) := Nat.sub_add_cancel (a₀₁)
   have a₁₂ : n - (k + 1) - 1 + 2 = n - (k + 1) + 1 := by omega
   have a₉ : n - (k + 1) - 1 + 1 + 2 = n - k + 1 := by omega
   have a₁₀ : n - (k + 1) - 1 + 1 ≤ n - 1 := by omega

   have h₂ : f (n - (k + 1) - 1 + 2, m + 1) ≠ 0 := by exact nzPattern_n.non_zero (n - (k + 1) - 1 + 2) (m + 1) a₃

   calc f (n - (k + 1) - 1, m + 2) =  f (n - (k + 1) - 1, m+2) * f (n - (k + 1) - 1 + 2, m + 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by rw [mul_inv_cancel_right₀ h₂ (f (n - (k + 1) - 1, m+2))]
            _= f (n - (k + 1) - 1 + 2, m + 1) * f (n - (k + 1) - 1, (m + 1) + 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by ring
            _= ( f (n - (k + 1) - 1 + 1, m + 1) * f (n - (k + 1) - 1 + 1, (m + 1) + 1) - 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by rw[pattern_n.diamond (n - (k + 1) - 1) (m+1) a₇]
            _= ( f (n - (k + 1) - 1 + 1, m + 1) * f (n - (k + 1) - 1 + 1, m + 2) - 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by simp
            _= ( f (n - (k + 1) - 1 + 1, m + 1) * f (n - k - 1, m + 2) - 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by rw[a₂]
            _= ( f (n - (k + 1) - 1 + 1, m + 1) * (f (n - 1, m + 2) * f (n - k, m + 1) - f (n - k + 1, m)) - 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ := by rw[← ih a₅]
            _= (f (n - 1, m + 2) * f (n - (k + 1) - 1 + 1, m + 1) * f (n - k, m + 1) - f (n - k + 1, m) * f (n - (k + 1) - 1 + 1, m + 1) - 1) * (f (n - (k + 1) - 1 + 2 , m + 1))⁻¹ := by ring
            _= (f (n - 1, m + 2) * f (n - (k + 1) - 1 + 1, m + 1) * f (n - k, m + 1) - f (n - (k + 1) - 1 + 1 + 2, m) * f (n - (k + 1) - 1 + 1, m + 1) - 1) * (f (n - (k + 1) - 1 + 2 , m + 1))⁻¹ := by rw[a₉]
            _= (f (n - 1, m + 2) * f (n - (k + 1) - 1 + 1, m + 1) * f (n - k, m + 1) - (f (n - (k + 1) - 1 + 1+1,m) * f (n - (k + 1) - 1 + 1 + 1, m + 1) - 1) - 1) * (f (n - (k + 1) - 1 + 2 , m + 1))⁻¹ := by rw[pattern_n.diamond (n - (k + 1) - 1 + 1) (m) a₁₀]
            _= f (n - 1, m + 2) * f (n - (k + 1) - 1 + 1, m + 1) * f (n - k, m + 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ - f (n - (k + 1) - 1 + 2,m) * f (n - (k + 1) - 1 + 2 , m + 1) * (f (n - (k + 1) - 1 + 2 , m + 1))⁻¹  := by ring
            _= f (n - 1, m + 2) * f (n - (k + 1), m + 1) * f (n - (k + 1) - 1 + 2, m + 1) * (f (n - (k + 1) - 1 + 2, m + 1))⁻¹ - f (n - (k + 1) - 1 + 2, m) * f (n - (k + 1) - 1 + 2 , m + 1) * (f (n - (k + 1) - 1 + 2 , m + 1))⁻¹  := by rw[a₁₁, a₁]
            _= f (n - 1, m + 2) * f (n - (k + 1), m + 1) - f (n - (k + 1) - 1 + 2, m) := by rw[mul_inv_cancel_right₀ h₂ (f (n - 1, m + 2) * f (n - (k + 1), m + 1)), mul_inv_cancel_right₀ h₂ (f (n - (k + 1) - 1 + 2, m))]
            _= f (n - 1, m + 2) * f (n - (k + 1), m + 1) - f (n - (k + 1) + 1, m) := by rw[a₁₂]
  --Have proved it in the case 1 ≤ n

  have n_eq_zero : n = 0 := by linarith
  intro i h m
  have i_leq_zero : i ≤ 0 := by omega
  have i_eq_zero : i = 0 := by linarith

  rw[i_eq_zero, n_eq_zero]
  simp
  rw[@pattern_n.topBordZeros F _ f n _ (m+2), @pattern_n.botBordZeros_n F _ f n _ (2) m (by linarith),zero_mul, sub_zero]
