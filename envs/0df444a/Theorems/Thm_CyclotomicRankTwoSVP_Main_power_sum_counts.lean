-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_power_sum_counts
-- name    : CyclotomicRankTwoSVP.Main.power_sum_counts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:07.888962+00:00
-- url     : https://prove2.me/theorems/9c1ecac0-1983-4e44-8b45-71c4ab123522
-- title:
--   Proposition 2.4 — all three uniform power-sum counts
-- statement:
--   Let $q$ be prime and $2\le k\le m-2<q-2$. For every prescribed moment vector $b\in\mathbb F_q^{k-1}$, let $X=X_{k,m}(b)$ be the tuples $z\in\mathbb F_q^m$ satisfying $\sum_r z_r^j=b_j$ for $1\le j<k$. Then
--
--   $$\big||X|-q^{m-k+1}\big|\le\tfrac12(2k)^m q^{(m-k+2)/2}.$$
--
--   For every distinct coordinate pair $i,\ell$, and every coordinate $i$ and field value $a$, respectively,
--
--   $$\big||\{z\in X:z_i=z_\ell\}|-q^{m-k}\big|\le\tfrac12(2k)^{m-1}q^{(m-k+2)/2},$$
--   $$\big||\{z\in X:z_i=a\}|-q^{m-k}\big|\le\tfrac12(2k)^{m-1}q^{(m-k+1)/2}.$$
--
--   All counts are uniform in $b$ and the specified coordinates. The powers with half-integer exponents are real powers; these estimates are the counting input to prescribed binary syndrome fibers.
--
--   Differences from the source:
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
--   - encoding: half-integer powers in the three real inequalities → real powers with division by two performed in R; reason: avoids truncated natural division and retains the printed exponents
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 8 / PDF p. 9, Proposition 2.4

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Arithmetic

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem power_sum_counts (q k m : ℕ) [Fact q.Prime]
    (hk : 2 ≤ k) (hkm : k ≤ m - 2) (hmq : m - 2 < q - 2)
    (b : Fin (k - 1) → ZMod q) :
    |((powerSumFiber q k m b).card : ℝ) - (q : ℝ) ^ (m - k + 1)| ≤
      (1 / 2 : ℝ) * (2 * k : ℝ) ^ m * (q : ℝ) ^ (((m : ℝ) - k + 2) / 2) ∧
    (∀ i l : Fin m, i ≠ l →
      |(((powerSumFiber q k m b).filter fun z => z i = z l).card : ℝ) - (q : ℝ) ^ (m - k)| ≤
        (1 / 2 : ℝ) * (2 * k : ℝ) ^ (m - 1) * (q : ℝ) ^ (((m : ℝ) - k + 2) / 2)) ∧
    (∀ (i : Fin m) (a : ZMod q),
      |(((powerSumFiber q k m b).filter fun z => z i = a).card : ℝ) - (q : ℝ) ^ (m - k)| ≤
        (1 / 2 : ℝ) * (2 * k : ℝ) ^ (m - 1) * (q : ℝ) ^ (((m : ℝ) - k + 1) / 2)) := by sorry

end CyclotomicRankTwoSVP.Main
