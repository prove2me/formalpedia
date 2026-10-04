-- Prove2me | Theorems.Thm_BJNAdAuctions_Basic_primal_dual_ratio
-- name    : BJNAdAuctions.Basic.primal_dual_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T16:36:58.964805+00:00
-- url     : https://prove2.me/theorems/e11860d9-6f83-4834-900c-c88deabf7181
-- title:
--   Theorem 1, proof, Claim (2): primal change is $1 + 1/(c-1)$ times dual change
-- statement:
--   Consider an instance of the online ad-auctions problem, a parameter $c > 1$ and any tie-breaking rule. In every iteration in which the Allocation Algorithm allocates product $j$ to buyer $i$, the covering cost increases by $B(i)\,\Delta x(i) + z(j) = b(i,j)\,(1 + 1/(c-1))$ and the packing profit increases by $b(i,j)$; in the other iterations neither changes. Summed over the run, with $x, y, z$ the final state,
--   $$
--   \sum_{i\in I} B(i)\,x(i) + \sum_{j=1}^m z(j) \;=\; \Big(1 + \frac{1}{c-1}\Big) \sum_{j=1}^m \sum_{i\in I} b(i,j)\,y(i,j).
--   $$
--
--   This is the second claim of the proof of Theorem 1; it converts the covering cost of the run into the packing profit of the run's own $y$.
--
--   **Formalization Note** The per-iteration ratio of the paper is $0/0$ on iterations that change nothing, so the claim is stated as the equivalent identity between the totals at the end of the run.
-- source:
--   Buchbinder, Jain & Naor, Online Primal-Dual Algorithms for Maximizing Ad-Auctions Revenue, ESA 2007, DOI 10.1007/978-3-540-75520-3_24, p. 7, Theorem 1, proof, Claim (2) and its displayed equation

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

namespace BJNAdAuctions.Basic

/-- Theorem 1, proof, Claim (2) (p. 7), summed over all iterations: every iteration that updates
the solutions raises the covering cost by `b(i, j) (1 + 1/(c - 1))` and the packing profit by
`b(i, j)`, so at the end of the run the covering cost equals `1 + 1/(c - 1)` times the packing
profit of the algorithm's own `y`. -/
theorem primal_dual_ratio {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} (inst : Instance I m)
    (c : ℝ) (hc : 1 < c) (sel : (I → ℝ) → Fin m → I) :
    coveringValue inst (run inst c sel).x (run inst c sel).z =
      (1 + 1 / (c - 1)) * packingValue inst (run inst c sel).y := by sorry

end BJNAdAuctions.Basic
