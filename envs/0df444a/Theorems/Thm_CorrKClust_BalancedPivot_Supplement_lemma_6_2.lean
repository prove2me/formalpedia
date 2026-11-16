-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_Supplement_lemma_6_2
-- name    : CorrKClust.BalancedPivot.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:29:27.028204+00:00
-- url     : https://prove2.me/theorems/471cd88b-e8af-4844-a173-237a04ab4279
-- title:
--   Lemma 6.2 — small loads at the kth pivot
-- statement:
--   Let $G$ be a disjoint union of $\ell>k\ge1$ nonempty cliques on $n\ge2$ vertices, and let $r=r(G)$ be the published peeling index. For any real $c>4$, let $S$ consist of the leading pivot clusters with load at most $4c\ln n$ at the arrival time $T_0$ of the $k$th pivot. Then
--   $$\Pr[|S|\ge k-r]\ge1-n^{1-c}-n^{-c/8}-n^{1-c/4}-n^{1-c/3}.$$
--   All four failure terms are retained. At $T_0$ these roots correspond bijectively to output clusters, so counting small roots counts $S$. This bound supplies enough destination clusters for UNIFORM PIVOT.
--
--   Differences from the source:
--   - encoding: the Section 6 disjoint-clique setup and clusters at T0 → n≥2, ℓ>k≥1, the original clique partition, and small leading pivots measured by pivotSize at kthPivotTime; reason: these are the section assumptions and the root-to-cluster bijection before any merging; no BALANCED PIVOT current load is substituted
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 6.2, p. 23

import Definitions.Def_CorrKClust_BalancedPivot_Supplement_Uniform

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

/-- Lemma 6.2, printed pp.23–24: all four failure terms, evaluated at T0, not T. -/
theorem lemma_6_2 (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k)
    (G : SimpleGraph (Fin n)) (Q : Fin n → Fin n) (hQ : IsCliquePartition G Q)
    (hℓ : k < (blocks Q).card) (c : ℝ) (hc : 4 < c) :
    1 - (n : ℝ) ^ (1 - c) - (n : ℝ) ^ (-c / 8) -
      (n : ℝ) ^ (1 - c / 4) - (n : ℝ) ^ (1 - c / 3) ≤
    probability (fun σ : ArrivalOrder (Fin n) =>
      k - cliqueR (blockSizes Q) k ≤
        (smallPivots G k σ (4 * c * Real.log n)).card) := by sorry

end CorrKClust.BalancedPivot.Supplement
