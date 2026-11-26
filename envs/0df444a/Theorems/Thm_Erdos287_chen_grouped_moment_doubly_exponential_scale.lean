-- Prove2me | Theorems.Thm_Erdos287_chen_grouped_moment_doubly_exponential_scale
-- name    : Erdos287.chen_grouped_moment_doubly_exponential_scale
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T17:23:25.418596+00:00
-- url     : https://prove2.me/theorems/dd2fa51a-bf02-5ece-b9f4-73fee26cc925
-- title:
--   A scale lower bound for the grouped Chen moment test in Erdős 287
-- statement:
--   Let the grouped sieve have $N=u+v$, $r=N/u$, $v/u<e$, pair coefficient $A\ge3.715$, and support radius $\sigma\le1/4$. Suppose the cofactor budget $B$ is certified by $B\operatorname{lcm}(1,\ldots,B)<p\le M$, and the form count satisfies $T\le2BN$. If the mean $\mu$ satisfies $N\mu\le2\sigma\log(1+T)$ and $1-A\sigma<\mu(r-A)$ with $A<r$, then $M>2^{2^{7800}}$.
-- source:
--   Erdős #287. Quantitative cofactor budget for a grouped sieve argument.

import Mathlib

theorem Erdos287.chen_grouped_moment_doubly_exponential_scale (B p M u v : ℕ) (T σ A μ : ℝ) (hu : 0 < u)
    (hv : (v : ℝ) < Real.exp 1 * (u : ℝ))
    (hB : B * Nat.lcmUpto B < p) (hp : p ≤ M)
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) (hA : 743 / 200 ≤ A) :
    let N : ℝ := (u : ℝ) + v
    let r := N / (u : ℝ)
    0 ≤ T ∧ T ≤ 2 * (B : ℝ) * N → A < r →
      N * μ ≤ 2 * σ * Real.log (1 + T) →
      1 - A * σ < μ * (r - A) → (2 : ℕ) ^ (2 ^ (7800 : ℕ)) < M := by sorry
