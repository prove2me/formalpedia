-- Prove2me | Theorems.Thm_Erdos3_leng_sah_sawhney
-- name    : Erdos3.leng_sah_sawhney
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:27:48.262966+00:00
-- url     : https://prove2.me/theorems/f74f8105-6eb7-4b54-a04f-a2bd2c0a796a
-- title:
--   Leng–Sah–Sawhney: $r_k(N)\le N\exp(-(\log\log N)^{c_k})$
-- statement:
--   **Leng–Sah–Sawhney.** For every $k\ge5$ there is $c_k>0$ such that for all sufficiently large $N$,
--
--   $$r_k(N)\ \le\ N\exp\!\bigl(-(\log\log N)^{c_k}\bigr),$$
--
--   where $r_k(N)$ is the largest size of a subset of $\{1,\dots,N\}$ with no non-trivial $k$-term arithmetic progression. (The source states the bound with an implied constant, which can be absorbed by shrinking $c_k$.) This is the current best general bound; it is still far from the $N/(\log N)^{1+c}$ that the goal would need via partial summation.
-- source:
--   J. Leng, A. Sah and M. Sawhney, *Improved bounds for Szemerédi's theorem*, arXiv:2402.17995 (2024), Theorem 1.1; cited at https://www.erdosproblems.com/3

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos3
open Erdos142

theorem leng_sah_sawhney (k : ℕ) (hk : 5 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-((Real.log (Real.log N)) ^ c)) := by
  sorry

end Erdos3
