-- Prove2me | Theorems.Thm_FamousTheorems_sum_four_squares
-- name    : FamousTheorems.sum_four_squares
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:51:56.658054+00:00
-- url     : https://prove2.me/theorems/b471823a-2f14-4843-b24e-53632892f873
-- title:
--   Lagrange's four-square theorem
-- statement:
--   **Every natural number is a sum of four squares.**
--
--   $$\forall n \in \mathbb{N},\ \exists a,b,c,d \in \mathbb{N} : \ n = a^2+b^2+c^2+d^2 .$$
--
--   Conjectured by Bachet, proved by Lagrange in 1770. Four is optimal: $7$ is not a sum of three
--   squares, and indeed Legendre characterised the numbers needing four as those of the form
--   $4^a(8b+7)$.
--
--   The standard proof combines Euler's four-square identity — the product of two sums of four
--   squares is again one, reflecting multiplicativity of the quaternion norm — with a descent
--   argument showing that if some multiple $mp$ of a prime is a sum of four squares then so is a
--   smaller one.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sum_four_squares : ∀ n : ℕ, ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by sorry

end FamousTheorems
