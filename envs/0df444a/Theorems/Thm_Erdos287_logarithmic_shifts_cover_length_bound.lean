-- Prove2me | Theorems.Thm_Erdos287_logarithmic_shifts_cover_length_bound
-- name    : Erdos287.logarithmic_shifts_cover_length_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:58:33.550611+00:00
-- url     : https://prove2.me/theorems/709571d2-8ad9-556c-8728-aabb3b99461d
-- title:
--   Grouping logarithmic shifts bounds the length covered by obstruction bands
-- statement:
--   Suppose every $x\in[a,b]$ is within $\varepsilon$ of a point $z+\log d$, where $1\le d\le N$ is an integer and one of the intervals $[l_i,u_i]$ contains $[z,z+r]$. Assume $u_i-l_i\ge r$ for every $i$. Then for every integer $1\le k\le N$,
--   $$
--   b-a\le\sum_i\left(k(u_i-l_i-r+2\varepsilon)+\log(N/k)\right).
--   $$
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Logarithmic-scale coverage from finite affine prime-tuple families.

import Mathlib

theorem Erdos287.logarithmic_shifts_cover_length_bound (J : Finset ℕ) (l u : ℕ → ℝ) (a b r ε : ℝ) (N k : ℕ)
    (hε : 0 ≤ ε) (hk : 1 ≤ k) (hkN : k ≤ N)
    (hl : ∀ i ∈ J, r ≤ u i - l i)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ i ∈ J, ∃ z ∈ Set.Icc (l i) (u i - r),
      ∃ d ∈ Finset.Icc 1 N, |x - (z + Real.log d)| ≤ ε) :
    b - a ≤ ∑ i ∈ J, ((k : ℝ) * (u i - l i - r + 2 * ε) +
      (Real.log (N : ℝ) - Real.log k)) := by sorry
