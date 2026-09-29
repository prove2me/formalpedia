-- Prove2me | Theorems.Thm_Erdos30_singer_lower_bound
-- name    : Erdos30.singer_lower_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:44:37.243828+00:00
-- url     : https://prove2.me/theorems/88666560-8a3b-46db-8559-ec5619e5d595
-- title:
--   Singer's lower bound: $h(N)\ge(1-o(1))\sqrt N$
-- statement:
--   For every $\varepsilon>0$ there is $N_0$ such that for all $N\ge N_0$,
--
--   $$h(N)\ \ge\ (1-\varepsilon)\sqrt N.$$
--
--   In other words $h(N)\ge(1-o(1))\sqrt N$. Singer's construction gives Sidon sets of size $q+1$ in $\{1,\dots,q^2+q+1\}$ for prime powers $q$; together with the fact that consecutive primes $p<p'$ satisfy $p'/p\to1$ this yields the bound for all $N$. Combined with the Erdős–Turán upper bound it shows $h(N)\sim\sqrt N$.
-- source:
--   Erdős Problem #30, https://www.erdosproblems.com/30: "Singer [Si38] was the first to show that h(N) ≥ (1−o(1))N^{1/2} for all N"; J. Singer, Trans. Amer. Math. Soc. 43 (1938), 377–385, https://doi.org/10.1090/S0002-9947-1938-1501951-4

import Mathlib
import Definitions.Def_Erdos30Basic

open Filter

namespace Erdos30

theorem singer_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (1 - ε) * Real.sqrt N ≤ (h N : ℝ) := by
  sorry

end Erdos30
