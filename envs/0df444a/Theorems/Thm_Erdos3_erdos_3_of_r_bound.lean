-- Prove2me | Theorems.Thm_Erdos3_erdos_3_of_r_bound
-- name    : Erdos3.erdos_3_of_r_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:30:34.109985+00:00
-- url     : https://prove2.me/theorems/a0fa394f-1242-48cb-abc5-1d3ae4a4bd71
-- title:
--   Reduction: $r_k(N)\le N/(\log N)^{1+c}$ for all $k$ implies the goal
-- statement:
--   **Partial-summation reduction.** Suppose that for every $k\ge3$ there is $c_k>0$ with $r_k(N)\le N/(\log N)^{1+c_k}$ for all large $N$. Then the goal holds. Indeed, if $A$ had no $k$-term progression then $|A\cap[1,N]|\le r_k(N)$ for all $N$, and partial summation gives
--
--   $$\sum_{n\in A,\ n\le N}\frac1n\ \le\ \frac{r_k(N)}{N}+\sum_{m< N}\frac{r_k(m)}{m(m+1)}\ \ll\ 1+\sum_{m}\frac{1}{m(\log m)^{1+c_k}}<\infty .$$
--
--   This is the standard route by which quantitative bounds for Szemerédi's theorem bear on Erdős Problem #3 (it is how Bloom–Sisask settle $k=3$).
-- source:
--   Standard partial-summation argument; see the remarks at https://www.erdosproblems.com/3 and Bloom–Sisask, arXiv:2007.03528 (2020), proof of Corollary 1.2

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos3
open Erdos142

theorem erdos_3_of_r_bound
    (h : ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r k N : ℝ) ≤ (N : ℝ) / (Real.log N) ^ (1 + c)) :
    ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, IsAPOfLength S k := by
  sorry

end Erdos3
