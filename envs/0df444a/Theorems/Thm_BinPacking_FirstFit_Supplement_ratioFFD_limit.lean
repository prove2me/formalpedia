-- Prove2me | Theorems.Thm_BinPacking_FirstFit_Supplement_ratioFFD_limit
-- name    : BinPacking.FirstFit.Supplement.ratioFFD_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:40:10.622043+00:00
-- url     : https://prove2.me/theorems/278875c1-60e9-4f06-9897-da3ec027b21e
-- title:
--   Theorem 4.4 — for $\alpha \in (1/5, 1/4]$, $\lim_{k\to\infty} R^\alpha_{FFD}(k) = 23/20$
-- statement:
--   For a list $L=(a_1,\dots,a_n)$ of real numbers in $(0,1]$ let $L^*$ be the least number of unit-capacity bins that can hold its elements, and $FFD(L)$ the number of bins used by **first-fit decreasing** (arrange $L$ into nonincreasing order, then place each element into the least-indexed bin with room for it). For $\alpha\in\mathbb R$ and $k\in\mathbb N$ let
--
--   $$
--   R^\alpha_{FFD}(k)=\sup\Big\{\frac{FFD(L)}{L^*}\;:\;L\subseteq(0,\alpha],\ L^*=k\Big\}
--   $$
--
--   be the worst-case ratio of first-fit decreasing on lists whose elements are all at most $\alpha$ and whose optimum is $k$.
--
--   **Theorem 4.4.** For every $\alpha$ with $1/5<\alpha\le 1/4$,
--
--   $$
--   \lim_{k\to\infty}R^\alpha_{FFD}(k)=\frac{23}{20}.
--   $$
--
--   Together with the paper's Corollary in §4 ($71/60$ on $(8/29,1/2]$ and $7/6$ on $(1/4,8/29]$) it describes how the asymptotic worst case of first-fit decreasing improves as the largest element size shrinks. The paper does not prove Theorem 4.4; it says "a similar (but more complicated) analysis can be given" and refers to Johnson's thesis [8].
--
--   **Formalization Note** $R^\alpha_{FFD}(k)$ is the definition `BinPacking.FirstFit.Supplement.ratioFFD`, a supremum in the extended nonnegative reals $[0,\infty]$ over lists with every element in $(0,1]$ and at most $\alpha$; the limit is convergence of the sequence $k\mapsto R^\alpha_{FFD}(k)$ to $23/20$ in $[0,\infty]$. The interval for $\alpha$ is open at $1/5$ and closed at $1/4$, as printed.
--
--   Differences from the source:
--   - encoding: R^α_FFD(k) as a real-valued maximum → a supremum in ℝ≥0∞ and convergence in ℝ≥0∞; reason: for each k ≥ 1 in the stated α interval the family is nonempty and Theorem 3.2 bounds its integer bin counts, so its supremum is an attained finite maximum; convergence to the finite value 23/20 agrees with real convergence.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 322, Theorem 4.4

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Supplement_ratioFFD

namespace BinPacking.FirstFit.Supplement

open Filter Topology
open scoped ENNReal

/-- Theorem 4.4 (Johnson et al. 1974, p. 322): for every `α ∈ (1/5, 1/4]`,
`lim_{k→∞} R^α_FFD(k) = 23/20`. -/
theorem ratioFFD_limit (α : ℝ) (hα : 1 / 5 < α) (hα4 : α ≤ 1 / 4) :
    Tendsto (ratioFFD α) atTop (𝓝 (23 / 20 : ℝ≥0∞)) := by sorry

end BinPacking.FirstFit.Supplement
