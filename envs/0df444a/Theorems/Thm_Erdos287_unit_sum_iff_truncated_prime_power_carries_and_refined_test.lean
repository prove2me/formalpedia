-- Prove2me | Theorems.Thm_Erdos287_unit_sum_iff_truncated_prime_power_carries_and_refined_test
-- name    : Erdos287.unit_sum_iff_truncated_prime_power_carries_and_refined_test
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:42:33.979801+00:00
-- url     : https://prove2.me/theorems/d1c72ab2-a773-50db-847d-15f6fad0433c
-- title:
--   Exact unit-sum criterion from truncated prime-power carries
-- statement:
--   Let $D$ be a finite set of positive integers dividing $L>0$, and let $Y>0$. Put $C=\operatorname{lcm}(1,\ldots,Y)$, $S=\sum_{n\in D}1/n$ and $W=\sum_{n\in D}L/n$. Fix a prime $p$ and a nonnegative integer $j$ with $|S-1|\gcd(L,C)<p^j$. Then $S=1$ if and only if both conditions hold. For every prime $r$, $r^{(v_r(L)-\lfloor\log_rY\rfloor)_+}$ divides $\sum_{n\in D\, :\,r^{v_r(n)}>Y}L/n$. At the chosen prime, $p^{(v_p(L)-\lfloor\log_pY\rfloor)_++j}$ divides $|W-L|$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.unit_sum_iff_truncated_prime_power_carries_and_refined_test (D : Finset ℕ) (L Y p j : ℕ) (hL : 0 < L) (hY : 0 < Y) (hp : p.Prime)
    (hD : ∀ n ∈ D, n ∣ L)
    (hbound : |(∑ n ∈ D, (1 : ℚ) / n) - 1| * (L.gcd (Nat.lcmUpto Y) : ℚ) < (p ^ j : ℕ)) :
    (∑ n ∈ D, (1 : ℚ) / n) = 1 ↔
      (∀ r : ℕ, r.Prime → r ^ (L.factorization r - r.log Y) ∣
        ∑ n ∈ D.filter (fun n => Y < r ^ n.factorization r), L / n) ∧
      p ^ (L.factorization p - p.log Y + j) ∣ Int.natAbs (((∑ n ∈ D, L / n : ℕ) : ℤ) - L) := by sorry
