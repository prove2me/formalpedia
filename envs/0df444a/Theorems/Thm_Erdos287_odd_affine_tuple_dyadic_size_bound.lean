-- Prove2me | Theorems.Thm_Erdos287_odd_affine_tuple_dyadic_size_bound
-- name    : Erdos287.odd_affine_tuple_dyadic_size_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:28:36.587897+00:00
-- url     : https://prove2.me/theorems/c83177d9-cf58-46df-a03f-c756670f1e3e
-- title:
--   Dyadic size bound for compatible odd affine tuples with arbitrary intercepts
-- statement:
--   Let a finite set of affine forms with positive leading coefficients have a common parameter $t$ at which all their values are odd. If each pair can be multiplied by positive cofactors so that their leading coefficients agree and their values at $t$ differ by one, then the leading coefficients have pairwise distinct valuations at $2$. Some slope is divisible by $2^{|S|-1}$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.odd_affine_tuple_dyadic_size_bound (S : Finset (ℕ × ℕ)) (t : ℕ) (hS : S.Nonempty)
    (hodd : ∀ q ∈ S, 0 < q.1 ∧ Odd (q.1 * t + q.2))
    (hpair : ∀ q ∈ S, ∀ r ∈ S, q ≠ r → ∃ c d : ℕ,
      0 < c ∧ 0 < d ∧ c * q.1 = d * r.1 ∧
      (c * (q.1 * t + q.2) + 1 = d * (r.1 * t + r.2) ∨
       d * (r.1 * t + r.2) + 1 = c * (q.1 * t + q.2))) :
    (∀ q ∈ S, ∀ r ∈ S, q ≠ r → padicValNat 2 q.1 ≠ padicValNat 2 r.1) ∧
    ∃ q ∈ S, 2 ^ (S.card - 1) ∣ q.1 := by sorry
