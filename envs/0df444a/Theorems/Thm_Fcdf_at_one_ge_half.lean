-- Prove2me | Theorems.Thm_Fcdf_at_one_ge_half
-- name    : Fcdf_at_one_ge_half
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T22:13:35.269301+00:00
-- url     : https://prove2.me/theorems/e7962502-97b1-4d56-80f6-b492518bd641
-- title:
--   Siegel median bound: $F(1)\ge\tfrac12$ for the homogeneous waiting time
-- statement:
--   **Siegel median bound for the homogeneous waiting-time CDF at $t=1$.** Consider the order-statistic waiting time $T$ where $N$ independent rate-$\lambda$ exponential clocks fire, with $\lambda=\log(N/m)$ (so $e^{-\lambda}=m/N$) and we wait for the $(N-m)$-th clock; its CDF is $F(s)=\sum_{k=N-m}^{N}\binom Nk(1-e^{-\lambda s})^k(e^{-\lambda s})^{N-k}$. The claim is $F(1)\ge \tfrac12$ for $1\le m<N$. This is the heart of the integer-mean binomial median theorem (Kaas–Buhrman / Jogdeo–Samuels): via Siegel's symmetrized-CDF (moustache) argument, the mean $\mu=\mathbb E[T]=\tfrac1\lambda\sum_{j=m+1}^N\tfrac1j<1$ satisfies $F(\mu)\ge\tfrac12$ (median $\le$ mean), and monotonicity of $F$ with $\mu<1$ gives $F(1)\ge F(\mu)\ge\tfrac12$. Source: Siegel, *Median Bounds and their Application*, J. Algorithms 38 (2001), Thm 2.1 (moustache value bound) and Thm 2.2 (homogeneous waiting-time model); equivalently Jogdeo–Samuels (Ann. Math. Statist. 39, 1968).

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators
open Finset

theorem Fcdf_at_one_ge_half (N m : ℕ) (h : m < N) (hm1 : 1 ≤ m) :
    (1/2 : ℝ) ≤ ∑ k ∈ Finset.Ico ((N-m-1)+1) (N+1),
      (Nat.choose N k : ℝ) * (1 - Real.exp (-(Real.log ((N:ℝ)/m) * 1))) ^ k
        * (Real.exp (-(Real.log ((N:ℝ)/m) * 1))) ^ (N - k) := by sorry
