-- Prove2me | Theorems.Thm_BanditAlgorithm_change_of_measure_deficit_pigeonhole_two_totals
-- name    : BanditAlgorithm.change_of_measure_deficit_pigeonhole_two_totals
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-04T04:12:00.379417+00:00
-- url     : https://prove2.me/theorems/4e538a91-2161-40d1-8ad4-cc2b2a734536
-- title:
--   Change-of-measure pigeonhole with separate deficit and penalty totals
-- statement:
--   Let $\iota$ be a finite index set of cardinality $k\ge 1$, and let $V,V^t,W:\iota\to\mathbb R$ with $V\ge 0$, $\sum_j V_j=T_0^{\mathrm{full}}$ and $\sum_j V^t_j=T_0$.  Suppose that for every $j$
--   $$W_j\;\ge\;T_0-V^t_j-B\sqrt{2V_j}.$$
--   Then some index $j$ satisfies $$W_j\;\ge\;\frac{(k-1)T_0-B\sqrt{2kT_0^{\mathrm{full}}}}{k}.$$
--
--   This is the change-of-measure summation step of Lattimore--Szepesv\'ari, *Bandit Algorithms*, section 38.7 (eq. 38.24), with the **deficit** and the **Pinsker penalty** carried by two different count vectors.  In the intended application the observable fed to the bounded change-of-measure inequality is a truncated count, because Step 2 needs it bounded by $\Theta(n/D)$ rather than by $n$; the divergence, however, is controlled by the *full* count of the $j$-th pair, since the two Markov decision processes differ in that pair's transition row at every round.  Hence the deficit $T_0-V^t_j$ uses the truncated counts, whose total $T_0$ is bounded below, while the Cauchy--Schwarz penalty uses the full counts, whose total $T_0^{\mathrm{full}}$ is only bounded above.  The single-total form is the special case $V^t=V$, $T_0^{\mathrm{full}}=T_0$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf, section 38.7, eq. (38.24) (printed p. 531, PDF p. 540); pattern of Exercise 15.2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Chebyshev

open Finset

theorem BanditAlgorithm.change_of_measure_deficit_pigeonhole_two_totals
    {ι : Type*} [Fintype ι] {k : ℕ} (hk : 0 < k) (hcard : Fintype.card ι = k)
    (V Vt W : ι → ℝ) (T0 T0full B : ℝ)
    (hV : ∀ j, 0 ≤ V j) (hsumV : ∑ j, V j = T0full) (hsumVt : ∑ j, Vt j = T0)
    (hB : 0 ≤ B)
    (hW : ∀ j, T0 - Vt j - B * Real.sqrt (2 * V j) ≤ W j) :
    ∃ j : ι,
      (((k : ℝ) - 1) * T0 - B * Real.sqrt (2 * k * T0full)) / k ≤ W j := by sorry
