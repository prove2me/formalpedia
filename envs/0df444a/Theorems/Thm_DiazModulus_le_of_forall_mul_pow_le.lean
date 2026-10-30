-- Prove2me | Theorems.Thm_DiazModulus_le_of_forall_mul_pow_le
-- name    : DiazModulus.le_of_forall_mul_pow_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:48.803722+00:00
-- url     : https://prove2.me/theorems/57d72586-7ca5-42f3-b81f-16330c9c5034
-- title:
--   Leading-coefficient extraction: if $a u^n \le b (u + c)^n$ for every integer $u \ge 1$, then $a \le b$
-- statement:
--   Let $a, b, c, n \in \mathbb{N}$. If $a u^n \le b (u + c)^n$ for every integer $u \ge 1$, then $a \le b$.
--
--   **Proof.** Dividing by $u^n$ gives $a \le b (1 + c/u)^n$ for every $u \ge 1$; as $u \to \infty$ the right side tends to $b$, and a bound that holds eventually passes to the limit.
--
--   **Novelty.** Classical; routine formalisation. It stands in for the leading-coefficient limits of DALAG §8.2.2 (p. 235) and of the proof of Th. 8.18 (p. 245).
-- source:
--   Elementary. A replacement for the limits defining the normalised leading coefficient in M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §8.2.2 (p. 235; Chapter 8 is by D. Roy). C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem le_of_forall_mul_pow_le (a b c n : ℕ) (h : ∀ u : ℕ, 1 ≤ u → a * u ^ n ≤ b * (u + c) ^ n) :
    a ≤ b := by
  sorry

end DiazModulus
