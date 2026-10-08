-- Prove2me | Theorems.Thm_Erdos3_bloom_sisask_bound
-- name    : Erdos3.bloom_sisask_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T17:22:48.694403+00:00
-- url     : https://prove2.me/theorems/3a73c56f-e244-428c-a81a-ba4c0ad8d572
-- title:
--   Bloom–Sisask: $r_3(N)\le N/(\log N)^{1+c}$
-- statement:
--   **Bloom–Sisask (breaking the logarithmic barrier).** There is an absolute $c>0$ such that for all sufficiently large $N$,
--
--   $$r_3(N)\ \le\ \frac{N}{(\log N)^{1+c}},$$
--
--   where $r_3(N)$ is the largest size of a subset of $\{1,\dots,N\}$ with no non-trivial three-term arithmetic progression. (The source states $r_3(N)\ll N/(\log N)^{1+c}$; an implied constant can be absorbed by shrinking $c$.) By partial summation this bound implies the case $k=3$ of the goal.
-- source:
--   T. F. Bloom and O. Sisask, *Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions*, arXiv:2007.03528 (2020), Theorem 1.1; cited at https://www.erdosproblems.com/3

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos3
open Erdos142

theorem bloom_sisask_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r 3 N : ℝ) ≤ (N : ℝ) / (Real.log N) ^ (1 + c) := by
  sorry

end Erdos3
