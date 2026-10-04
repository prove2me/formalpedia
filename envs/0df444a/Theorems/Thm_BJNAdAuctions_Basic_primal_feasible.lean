-- Prove2me | Theorems.Thm_BJNAdAuctions_Basic_primal_feasible
-- name    : BJNAdAuctions.Basic.primal_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T16:32:28.499947+00:00
-- url     : https://prove2.me/theorems/8fead732-e8c1-4e5a-8e82-d7dc724f61fa
-- title:
--   Theorem 1, proof, Claim (1): the algorithm produces a primal feasible solution
-- statement:
--   Consider an instance of the online ad-auctions problem with a nonempty set of buyers, a parameter $c > 1$, and any argmax tie-breaking rule. Let $x$ be the covering vector at the end of the run of the Allocation Algorithm and $z$ the vector with $z(j)$ as set when product $j$ arrived ($z(j) = 0$ if the product was not sold). Then $(x, z)$ is feasible for the covering LP of Fig. 2:
--   $$
--   b(i,j)\,x(i) + z(j) \ge b(i,j) \quad \text{for all } i, j, \qquad x \ge 0, \qquad z \ge 0.
--   $$
--
--   This is the first of the three claims on which the proof of Theorem 1 rests; together with weak duality it lets the covering cost of the run bound every packing solution.
-- source:
--   Buchbinder, Jain & Naor, Online Primal-Dual Algorithms for Maximizing Ad-Auctions Revenue, ESA 2007, DOI 10.1007/978-3-540-75520-3_24, p. 7, Theorem 1, proof, Claim (1)

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

namespace BJNAdAuctions.Basic

/-- Theorem 1, proof, Claim (1) (p. 7): the final covering vector `x` and the vector `z` produced
by the Allocation Algorithm form a feasible solution of the covering LP of Fig. 2, for every
parameter `c > 1` and every tie-breaking of the argmax. -/
theorem primal_feasible {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} (inst : Instance I m)
    (c : ℝ) (hc : 1 < c) (sel : (I → ℝ) → Fin m → I) (hsel : IsArgmaxRule inst sel) :
    CoveringFeasible inst (run inst c sel).x (run inst c sel).z := by sorry

end BJNAdAuctions.Basic
