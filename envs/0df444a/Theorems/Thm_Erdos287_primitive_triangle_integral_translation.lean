-- Prove2me | Theorems.Thm_Erdos287_primitive_triangle_integral_translation
-- name    : Erdos287.primitive_triangle_integral_translation
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:05:28.854735+00:00
-- url     : https://prove2.me/theorems/38fb4785-29ef-493a-8203-7cbb04fd07d8
-- title:
--   Integral translation for a primitive triangle determinant system
-- statement:
--   Let $s_1,s_2,s_3$ be natural numbers with common gcd one. If two integer triples $x$ and $y$ have the same values of $s_j x_i-s_i x_j$ and $s_j y_i-s_i y_j$ for all $i<j$, then $x_i=y_i+s_i t$ for a single integer $t$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.primitive_triangle_integral_translation (s₁ s₂ s₃ : ℕ) (x₁ x₂ x₃ y₁ y₂ y₃ : ℤ)
    (hprim : Nat.gcd (Nat.gcd s₁ s₂) s₃ = 1)
    (h₁₂ : (s₂ : ℤ) * x₁ - (s₁ : ℤ) * x₂ = (s₂ : ℤ) * y₁ - (s₁ : ℤ) * y₂)
    (h₁₃ : (s₃ : ℤ) * x₁ - (s₁ : ℤ) * x₃ = (s₃ : ℤ) * y₁ - (s₁ : ℤ) * y₃)
    (h₂₃ : (s₃ : ℤ) * x₂ - (s₂ : ℤ) * x₃ = (s₃ : ℤ) * y₂ - (s₂ : ℤ) * y₃) :
    ∃ t : ℤ, x₁ = y₁ + (s₁ : ℤ) * t ∧
      x₂ = y₂ + (s₂ : ℤ) * t ∧ x₃ = y₃ + (s₃ : ℤ) * t := by sorry
