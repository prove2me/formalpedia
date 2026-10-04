-- Prove2me | Theorems.Thm_BJNAdAuctions_Basic_almost_dual_feasible
-- name    : BJNAdAuctions.Basic.almost_dual_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T16:45:52.411408+00:00
-- url     : https://prove2.me/theorems/3bc97140-aee5-4a95-bbc6-0e80c4c6ec41
-- title:
--   Theorem 1, proof, Claim (3): the algorithm produces an almost feasible dual solution
-- statement:
--   Let $R > 0$ be such that $b(i,j) \le R\,B(i)$ for all $i, j$, and run the Allocation Algorithm with $c = (1+R)^{1/R}$ and any tie-breaking rule. Then for every buyer $i$, with $y$ the final packing vector and $\mathrm{spent}(i)$ the total amount charged to $i$:
--
--   1. the bids allocated to $i$ exceed its budget by at most one bid,
--   $$
--   \sum_{j=1}^m b(i,j)\,y(i,j) \;\le\; B(i) + \max_{j} b(i,j);
--   $$
--   2. the profit extracted from $i$ is at least a $(1-R)$ fraction of them,
--   $$
--   \mathrm{spent}(i) \;\ge\; (1-R) \sum_{j=1}^m b(i,j)\,y(i,j).
--   $$
--
--   This is the third claim of the proof of Theorem 1: the run's $y$ is feasible for the packing LP up to one bid per buyer, and the revenue loses at most a factor $1 - R$ against its packing value.
--
--   **Formalization Note** $\max_j b(i,j)$ is `⨆ j, inst.b i j` over the finite type `Fin m`; for $m = 0$ it is $0$, which is also the value of the left-hand side.
-- source:
--   Buchbinder, Jain & Naor, Online Primal-Dual Algorithms for Maximizing Ad-Auctions Revenue, ESA 2007, DOI 10.1007/978-3-540-75520-3_24, pp. 7-8, Theorem 1, proof, Claim (3) and the inequalities closing its proof

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

namespace BJNAdAuctions.Basic

/-- Theorem 1, proof, Claim (3) in quantitative form (pp. 7–8): with `c = (1 + R)^(1/R)`, where
every bid is at most `R` times its buyer's budget, each buyer `i` receives allocated bids
`∑_j b(i, j) y(i, j)` of total at most `B(i) + max_j b(i, j)`, and the amount charged to `i` is at
least `(1 - R) ∑_j b(i, j) y(i, j)`. -/
theorem almost_dual_feasible {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} (inst : Instance I m)
    (R : ℝ) (hR : 0 < R) (hbR : ∀ i j, inst.b i j ≤ R * inst.B i)
    (sel : (I → ℝ) → Fin m → I) (i : I) :
    ∑ j, inst.b i j * (run inst ((1 + R) ^ (1 / R)) sel).y i j ≤ inst.B i + (⨆ j, inst.b i j) ∧
    (1 - R) * ∑ j, inst.b i j * (run inst ((1 + R) ^ (1 / R)) sel).y i j ≤
      (run inst ((1 + R) ^ (1 / R)) sel).spent i := by sorry

end BJNAdAuctions.Basic
