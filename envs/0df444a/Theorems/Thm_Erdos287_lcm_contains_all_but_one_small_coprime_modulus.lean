-- Prove2me | Theorems.Thm_Erdos287_lcm_contains_all_but_one_small_coprime_modulus
-- name    : Erdos287.lcm_contains_all_but_one_small_coprime_modulus
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:46:55.868594+00:00
-- url     : https://prove2.me/theorems/884f6cb3-3dd1-5479-8c10-18240f6af592
-- title:
--   Coprime divisibility classes forced by gaps at most two
-- statement:
--   Suppose $D$ contains at least one member of every consecutive pair in $[\ell,h]$. If positive coprime integers $a,b$ have $ab\le h-\ell$, at least one divides $\operatorname{lcm}(D)$. Consequently, for any pairwise coprime family of positive moduli at most $K$ with $K^2\le h-\ell$, at most one modulus fails to divide $\operatorname{lcm}(D)$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. The arithmetic proof uses the Chinese remainder theorem.

import Mathlib

theorem Erdos287.lcm_contains_all_but_one_small_coprime_modulus (D : Finset ℕ) (lo hi : ℕ)
    (hcover : ∀ x, lo ≤ x → x + 1 ≤ hi → x ∈ D ∨ x + 1 ∈ D) :
    (∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a * b ≤ hi - lo →
      a ∣ D.lcm id ∨ b ∣ D.lcm id) ∧
    (∀ (P : Finset ℕ) (K : ℕ), K * K ≤ hi - lo →
      (∀ a ∈ P, 0 < a ∧ a ≤ K) →
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → Nat.Coprime a b) →
      (P.filter fun a => ¬ a ∣ D.lcm id).card ≤ 1) := by sorry
