-- Prove2me | Theorems.Thm_ConantTerry_Orders_Supplement_theorem_5_2
-- name    : ConantTerry.Orders.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:27:19.975226+00:00
-- url     : https://prove2.me/theorems/46080b3b-66e7-4bfe-be11-1c7f246ee318
-- title:
--   Theorem 5.2 — ordinary trees from agnostic trees
-- statement:
--   Let $X,Y$ be arbitrary sets, $f:X\times Y\to[0,1]$, $t\ge1$, $\delta>0$ and $0<\epsilon<1$. Set $K=\lceil2/\epsilon\rceil$ and $T=\sum_{i=0}^{t-1}K^i=(K^t-1)/(K-1)$. Then
--   $$
--   f\text{ admits an agnostic }(T,\delta+\epsilon)\text{-tree}\quad\Longrightarrow\quad
--   f\text{ admits a }(t,\delta)\text{-tree}.
--   $$
--   The input tests the absolute difference for every opposite-branch pair of leaves. The output is an ordinary tree with node-dependent thresholds allowed; no uniformity is claimed.
--
--   This companion theorem expresses the approximate conversion between the agnostic and oriented tree notions and uses Lemma 2.7. It is not used in the proof of the goal Theorem 1.11.
--
--   Differences from the source:
--   - encoding: arbitrary sets X,Y and values in [0,1] → arbitrary types X,Y and the real subtype Set.Icc 0 1; reason: the subtype enforces exactly the source range and adds no finiteness, nonemptiness or regularity assumption
--   - encoding: finite binary words and 1-based finite indices → published List Bool word subtypes and zero-based Fin indices; reason: length, prefix, orientation and index inequalities are preserved by relabeling
--   - encoding: T=(ceil(2/ε)^t−1)/(ceil(2/ε)−1) → T=Σ_{i<t}ceil(2/ε)^i; reason: the geometric identity is exact and K≥3 on 0<ε<1, so the denominator is positive; finite sums avoid default division values
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p. 19, Theorem 5.2; proof pp. 19–20

import Mathlib
import Definitions.Def_ConantTerry_Orders_function_tree
import Definitions.Def_ConantTerry_Orders_Supplement_agnostic_tree
import Definitions.Def_ConantTerry_Orders_Supplement_extraction_heights

namespace ConantTerry.Orders.Supplement

/-- Theorem 5.2, pp.19-20. The ordinary output tree can have node-dependent
thresholds. The exact geometric sum is the printed quotient. -/
theorem theorem_5_2 {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (t : ℕ) (ht : 1 ≤ t)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεsmall : ε < 1)
    (htree : AdmitsAgnosticTree f (agnosticHeight t ε) (δ + ε)) :
    AdmitsTree f t δ := by sorry

end ConantTerry.Orders.Supplement
