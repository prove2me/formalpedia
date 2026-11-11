-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_equation_29
-- name    : CorrKClust.BalancedPivot.equation_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:36.175731+00:00
-- url     : https://prove2.me/theorems/01e0c7dc-6a3f-4565-be96-81e697ee4670
-- title:
--   §7.3.4, (29) — K₀ is at most nine times the k-clustering optimum
-- statement:
--   Let $G$ be a finite graph, let $k\ge1$, and fix any optimal unconstrained partition Q with more than k nonempty blocks. Complete its blocks into disjoint cliques to form I_clique. Let $s_0=s(I_{clique})$, $a_0=a(I_{clique})$ and let e_m count missing edges inside Q's blocks. Then
--   $$K_0:=s_0a_0+e_m\le9\operatorname{OPT}_k(G).$$
--   The partition is chosen independently of arrival order, and the result holds for every optimal Q. The explicit constant is 9, even though the selected lower bound permits a sharper inequality.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: at most k possibly empty clusters → k > 0 and assignments V → Fin k; reason: positive k is required for an assignment on nonempty inputs and all unused labels remain legal
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), §7.3.4, equation (29), p. 44, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- §7.3.4, (29), p. 44: fixed optimal CC partition, exact constant 9. -/
theorem equation_29 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k : ℕ} (hk : 0 < k)
    (Q : V → V) (hQ : cost G Q = optCC G) (hq : k < (blocks Q).card) :
    (cliqueS (blockSizes Q) k : ℝ) * cliqueA (blockSizes Q) k + (missingEdges G Q : ℝ) ≤
      9 * (optK G k : ℝ) := by sorry

end CorrKClust.BalancedPivot
