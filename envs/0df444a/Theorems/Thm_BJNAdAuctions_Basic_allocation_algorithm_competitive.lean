-- Prove2me | Theorems.Thm_BJNAdAuctions_Basic_allocation_algorithm_competitive
-- name    : BJNAdAuctions.Basic.allocation_algorithm_competitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T17:01:25.433489+00:00
-- url     : https://prove2.me/theorems/c5c2e6ca-e494-4cc1-85aa-bfce8a68a43c
-- title:
--   Theorem 1 — the Allocation Algorithm is $(1 - 1/c)(1 - R_{\max})$-competitive
-- statement:
--   Consider an instance of the online ad-auctions problem with a nonempty finite set $I$ of buyers, budgets $B(i) > 0$ and bids $b(i,j) \ge 0$ on $m$ products. Let $R > 0$ bound the bid-to-budget ratios, $b(i,j) \le R\,B(i)$ for all $i, j$, and let
--   $$
--   c = (1 + R)^{1/R}.
--   $$
--   Run the Allocation Algorithm with parameter $c$ and any tie-breaking rule that picks a buyer maximizing $b(i,j)(1 - x(i))$. Then for every feasible solution $y'$ of the packing LP of Fig. 2, the revenue collected by the algorithm satisfies
--   $$
--   \mathrm{Revenue} \;\ge\; \Big(1 - \frac{1}{c}\Big)(1 - R) \sum_{j=1}^m \sum_{i\in I} b(i,j)\,y'(i,j).
--   $$
--
--   Taking $R = R_{\max} = \max_{i,j} b(i,j)/B(i)$ (when positive) gives the paper's Theorem 1: the Allocation Algorithm is $(1 - 1/c)(1 - R_{\max})$-competitive with $c = (1 + R_{\max})^{1/R_{\max}}$. The bound is against the optimum of the fractional LP, which is at least the revenue of any integral offline allocation, so it implies the competitive ratio against the integral offline optimum. Since the algorithm is deterministic and the statement holds for every instance, it holds against every adversary.
--
--   **Formalization Note** The revenue is `revenue inst c sel`, the sum over buyers of the amounts charged by the run that `AllocationAlgorithm` computes from the instance; the tie-breaking rule `sel` is universally quantified subject to the argmax property. The statement is for any bound $R$ on the ratios, not only their exact maximum; the exact maximum is one admissible choice.
-- source:
--   Buchbinder, Jain & Naor, Online Primal-Dual Algorithms for Maximizing Ad-Auctions Revenue, ESA 2007, DOI 10.1007/978-3-540-75520-3_24, p. 7, Theorem 1

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

namespace BJNAdAuctions.Basic

/-- **Theorem 1** (p. 7), first sentence: the Allocation Algorithm is
`(1 - 1/c)(1 - R_max)`-competitive, where `c = (1 + R_max)^(1/R_max)`. Stated for any bound
`R > 0` with `b(i, j) ≤ R · B(i)` for all `i, j` (the exact `R_max` is one such bound), for every
tie-breaking of the argmax, against every feasible solution `y'` of the fractional packing LP of
Fig. 2 (whose optimum bounds the integral offline optimum from above). -/
theorem allocation_algorithm_competitive {I : Type*} [Fintype I] [Nonempty I] {m : ℕ}
    (inst : Instance I m) (R : ℝ) (hR : 0 < R) (hbR : ∀ i j, inst.b i j ≤ R * inst.B i)
    (sel : (I → ℝ) → Fin m → I) (hsel : IsArgmaxRule inst sel)
    (y' : I → Fin m → ℝ) (hy' : PackingFeasible inst y') :
    (1 - 1 / (1 + R) ^ (1 / R)) * (1 - R) * packingValue inst y' ≤
      revenue inst ((1 + R) ^ (1 / R)) sel := by sorry

end BJNAdAuctions.Basic
