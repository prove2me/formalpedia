-- Prove2me | solution 1 for shannon_capacity_c5
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:38:00.55203+00:00
-- url     : https://prove2.me/submissions/1771eb86-46ab-4968-9da4-e41b8ffc77ab

import Mathlib

theorem solution :
    ∃ (cap : ℝ),
      cap = Real.sqrt 5 ∧
      ∀ eps : ℝ, 0 < eps →
      ∃ N : ℕ, ∀ (n : ℕ) (_ : N ≤ n) (ind : Fin n → Fin 5),
        (∀ i j : Fin n, i ≠ j →
          (ind i).val = (ind j).val ∨ (ind i).val + 1 ≡ (ind j).val [MOD 5]) →
        (n : ℝ) ≤ (cap + eps) ^ n := by
  refine ⟨Real.sqrt 5, rfl, fun eps heps => ⟨0, fun n _ ind _ => ?_⟩⟩
  have h2 : (2 : ℝ) ≤ Real.sqrt 5 + eps := by
    have h4 : (2 : ℝ) ≤ Real.sqrt 5 := by
      have : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [← this]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  calc (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    _ ≤ (Real.sqrt 5 + eps) ^ n := pow_le_pow_left₀ (by norm_num) h2 n
