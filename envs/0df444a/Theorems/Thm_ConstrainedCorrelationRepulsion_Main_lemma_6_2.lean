-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_6_2
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:19.677571+00:00
-- url     : https://prove2.me/theorems/df984e7d-e550-47ec-bf5a-8fde2aa88000
-- title:
--   Lemma 6.2 — almost-sure termination and first-hit cost, including the pointwise bound
-- statement:
--   Run independent rounds from the original fixed candidate law, intersecting with the remaining set before radius-one repair. The infinite run processes every vertex in finite time almost surely, and its partition is feasible. Write $a_{uv}$ for the positive-label indicator, $x_{uv}$ for the LP distance, $Z$ for the sum of empty-index LP masses, and $b$ for the capped function in (31). With the actual pair probability $q_{uv}$,
--
--   $$
--   \mathbb E\mathrm{cost}_{I'}(\mathrm{ALG}_\infty)\le\sum_{uv\notin H}F_{a_{uv}}(x_{uv},Zq_{uv}),\quad F_a(x,y)=\frac{2a(1-y)+(1-a+ab(x))y}{2-y}.
--   $$
--
--   For every $a\in\{0,1\}$ and $x,y\in[0,1]$, put $d=y-(1-x)$. The additional pointwise conclusion is $F_a(x,y)\le2ax+(1-a)(1-x)+d+3a|d|$. The expectation is over the countable product of the actual candidate law.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - generalization: units obtained by the preclustering procedure → any unit partition satisfying the stated residual structural conditions; reason: these conclusions use normalized labels, hard cross-products and local LP constraints; atom optimality and the free-degree budget are not used
--   - encoding: real expectations of conditional inclusion values → extended nonnegative sums of conditional inclusion values; reason: reachable inclusion values lie in [0,1] and the sampler has finite support, so these equalities are equivalent to the ordinary real expectations
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 6.2, equations (37)–(39), printed p.32 (PDF p.33)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Rounds

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_6_2 {n : ℕ} (I : Instance n) (U : Units n) (r : ℕ)
    (y : LocalTable n) (hn : 0 < n) (hr : 6 ≤ r) (heven : Even r)
    (hres : ResidualUnits I U) (hy : BoundedOptimal I U r y) (hq : RationalTable y) :
  (∀ᵐ stream ∂streamMeasure (candidateLaw I U y r),
    (∃ T, processedBefore stream T = Finset.univ) ∧
    Feasible I (infinitePartition I (tableDistance U y) stream)) ∧
  (let charge := pairSum (fun u v => if I.cannotLink.Adj u v then 0 else
    firstHitCharge (if I.positive.Adj u v then 1 else 0) (tableDistance U y u v) (Z y * qActual I U y r u v))
   0 ≤ charge ∧ infiniteExpectedCost I U y r ≤ ENNReal.ofReal charge) ∧
  (∀ a x z : ℝ, (a = 0 ∨ a = 1) → 0 ≤ x → x ≤ 1 → 0 ≤ z → z ≤ 1 →
    firstHitCharge a x z ≤ 2*a*x + (1-a)*(1-x) + (z-(1-x)) + 3*a*|z-(1-x)|) := by sorry

end ConstrainedCorrelationRepulsion.Main
