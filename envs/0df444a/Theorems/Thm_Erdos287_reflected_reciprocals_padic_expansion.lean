-- Prove2me | Theorems.Thm_Erdos287_reflected_reciprocals_padic_expansion
-- name    : Erdos287.reflected_reciprocals_padic_expansion
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:51:57.955004+00:00
-- url     : https://prove2.me/theorems/24902bb8-0e42-4714-aa0e-b58ac3eebe3c
-- title:
--   Higher-order p-adic congruences for symmetric reciprocal pairs
-- statement:
--   Suppose $p$ is prime, $p^e\mid c$ with $e\ge1$, and the positive offsets $d$ in a finite set $T$ satisfy $d<c$ and $p\nmid d$. For $r\ge0$ the $p$-adic norm of the sum over $d\in T$ of $1/(c-d)+1/(c+d)+(2c/d^2)\sum_{j<r}(c^2/d^2)^j$ is at most $p^{-(2r+1)e}$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.reflected_reciprocals_padic_expansion (T : Finset ℕ) (p c e r : ℕ) (hp : p.Prime)
    (he : 1 ≤ e) (hc : p ^ e ∣ c)
    (hT : ∀ d ∈ T, 0 < d ∧ d < c ∧ ¬ p ∣ d) :
    padicNorm p (∑ d ∈ T,
      (((1 : ℚ) / ((c : ℚ) - d) + (1 : ℚ) / ((c : ℚ) + d)) +
        ((2 : ℚ) * c / (d : ℚ) ^ 2) *
          (∑ j ∈ Finset.range r, ((c : ℚ) ^ 2 / (d : ℚ) ^ 2) ^ j))) ≤
      (p : ℚ) ^ (-(((2 * r + 1) * e : ℕ) : ℤ)) := by sorry
