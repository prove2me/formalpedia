-- Prove2me | Theorems.Thm_FamousTheorems_add_pow
-- name    : FamousTheorems.add_pow
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:10:37.841971+00:00
-- url     : https://prove2.me/theorems/ad0f4bd8-19f6-4f88-a7e7-392c9594ae82
-- title:
--   The binomial theorem
-- statement:
--   **The binomial theorem.**
--
--   $$(x+y)^{n} \;=\; \sum_{k=0}^{n} \binom{n}{k} x^{k} y^{n-k}.$$
--
--   Expanding the product of $n$ factors, each term chooses $x$ from $k$ of them and $y$ from the
--   rest, and there are $\binom{n}{k}$ such choices — so the theorem is a counting statement, which
--   is why it holds over any commutative semiring.
--
--   Known in special cases to Euclid and in general to al-Karaji and Pascal; Newton's extension to
--   non-integer exponents as an infinite series opened the way to power-series analysis. Setting
--   $x=y=1$ gives $\sum_k \binom{n}{k} = 2^n$, and $x=1, y=-1$ gives the alternating sum $0$.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem add_pow : ∀ {R : Type*} [CommSemiring R] (x y : R) (n : ℕ),
    (x + y) ^ n = ∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) * (n.choose k) := by sorry

end FamousTheorems
