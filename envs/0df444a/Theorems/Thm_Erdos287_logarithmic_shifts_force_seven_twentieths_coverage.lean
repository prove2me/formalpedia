-- Prove2me | Theorems.Thm_Erdos287_logarithmic_shifts_force_seven_twentieths_coverage
-- name    : Erdos287.logarithmic_shifts_force_seven_twentieths_coverage
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:03:56.036628+00:00
-- url     : https://prove2.me/theorems/0cd6cccd-2bc8-44e0-91eb-6d81fd42c403
-- title:
--   Two logarithmic shift groupings force a seven-twentieths length bound
-- statement:
--   Suppose $3\le N\le49$. There exist $0<r<1$ and $\varepsilon>0$ with the following property. If an interval $[a,b]$ is within $\varepsilon$ of points $z+\log d$, $1\le d\le N$, where every such start $z$ has $[z,z+r]$ contained in one of the intervals $[l_i,u_i]$ of length at least $r$, then $7(b-a)\le20\sum_i(u_i-l_i)$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. A weighted combination of two finite logarithmic coverage estimates.

import Mathlib

theorem Erdos287.logarithmic_shifts_force_seven_twentieths_coverage (N : ℕ) (hN : 3 ≤ N) (hN₄₉ : N ≤ 49) :
    ∃ r ε : ℝ, 0 < r ∧ r < 1 ∧ 0 < ε ∧
      ∀ (J : Finset ℕ) (l u : ℕ → ℝ) (a b : ℝ),
        (∀ i ∈ J, r ≤ u i - l i) →
        (∀ x ∈ Set.Icc a b, ∃ i ∈ J, ∃ z ∈ Set.Icc (l i) (u i - r),
          ∃ d ∈ Finset.Icc 1 N, |x - (z + Real.log d)| ≤ ε) →
        7 * (b - a) ≤ 20 * ∑ i ∈ J, (u i - l i) := by sorry
