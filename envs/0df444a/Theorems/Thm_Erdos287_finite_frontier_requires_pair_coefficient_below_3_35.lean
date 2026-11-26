-- Prove2me | Theorems.Thm_Erdos287_finite_frontier_requires_pair_coefficient_below_3_35
-- name    : Erdos287.finite_frontier_requires_pair_coefficient_below_3_35
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T16:01:53.180024+00:00
-- url     : https://prove2.me/theorems/6b5320e0-1972-5d29-9724-a7e5712b4068
-- title:
--   Finite frontier requires a pair coefficient below 3.35
-- statement:
--   Let $N=u+v$, $r=N/u$ with $u>0$ and $v<eu$. Suppose the cofactor budget is $B\le3187$, the total number of forms is $0\le T\le2BN$, and $0\le\sigma\le1/4$. If the normalized mean satisfies $N\mu\le2\sigma\log(1+T)$ and the pair coefficient satisfies $3.35\le A<r$, then $\mu(r-A)\le1-A\sigma$. Thus this one-period moment test cannot certify an adjacent omission.
-- source:
--   Erdős #287 finite-to-asymptotic sieve analysis.

import Mathlib

theorem Erdos287.finite_frontier_requires_pair_coefficient_below_3_35 (B u v : ℕ) (T σ A μ : ℝ) (hB : B ≤ 3187) (hu : 0 < u)
    (hv : (v : ℝ) < Real.exp 1 * (u : ℝ))
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) (hA : 67 / 20 ≤ A) :
    let N : ℝ := (u : ℝ) + v
    let r := N / (u : ℝ)
    0 ≤ T ∧ T ≤ 2 * (B : ℝ) * N → A < r →
      N * μ ≤ 2 * σ * Real.log (1 + T) → μ * (r - A) ≤ 1 - A * σ := by sorry
