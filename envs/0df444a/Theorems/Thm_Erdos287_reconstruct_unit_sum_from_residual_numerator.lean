-- Prove2me | Theorems.Thm_Erdos287_reconstruct_unit_sum_from_residual_numerator
-- name    : Erdos287.reconstruct_unit_sum_from_residual_numerator
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:38:58.268915+00:00
-- url     : https://prove2.me/theorems/b131a68d-26b0-4e38-b467-348ff85ac58a
-- title:
--   Exact unit-sum reconstruction from the residual numerator
-- statement:
--   Let $L>0$ and put $G=\gcd(L,C)$ and $K=L/G$. Suppose $|W/L-1|G<q$. Then $W/L=1$ if and only if its reduced denominator divides $C$ and $\lfloor W/K\rfloor\equiv G\pmod q$. The bound and denominator cap suffice for any modulus $q$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.reconstruct_unit_sum_from_residual_numerator (W L C q : ℕ) (hL : 0 < L)
    (hbound : |(W : ℚ) / L - 1| * (L.gcd C : ℚ) < q) :
    (W : ℚ) / L = 1 ↔
      ((W : ℚ) / L).den ∣ C ∧ W / (L / L.gcd C) ≡ L.gcd C [MOD q] := by sorry
