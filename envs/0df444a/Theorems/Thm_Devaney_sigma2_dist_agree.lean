-- Prove2me | Theorems.Thm_Devaney_sigma2_dist_agree
-- name    : Devaney.sigma2_dist_agree
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:27:40.124113+00:00
-- url     : https://prove2.me/theorems/e6af4933-098a-440c-ac1d-7a389f40d155
-- title:
--   Proposition 6.3 — closeness in $\Sigma_2$ means agreeing on an initial block
-- statement:
--   Let $s, t \in \Sigma_2$ and $n \ge 0$, with the metric $d[s,t] = \sum_i |s_i - t_i| 2^{-i}$.
--
--   1. If $s_i = t_i$ for all $i \le n$, then $d[s,t] \le 1/2^{n}$.
--   2. Conversely, if $d[s,t] < 1/2^{n}$, then $s_i = t_i$ for all $i \le n$.
--
--   This is the workhorse of symbolic dynamics: it converts the analytic statement "two sequences are close" into the combinatorial statement "two sequences agree on a long initial block", and back.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.6, p. 41, Proposition 6.3

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem sigma2_dist_agree (s t : Sigma2) (n : ℕ) :
    ((∀ i ≤ n, s i = t i) → dist s t ≤ 1 / 2 ^ n) ∧
      (dist s t < 1 / 2 ^ n → ∀ i ≤ n, s i = t i) := by sorry
end Devaney
