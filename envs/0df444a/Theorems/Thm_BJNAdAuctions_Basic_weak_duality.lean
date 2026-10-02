-- Prove2me | Theorems.Thm_BJNAdAuctions_Basic_weak_duality
-- name    : BJNAdAuctions.Basic.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T16:50:22.912541+00:00
-- url     : https://prove2.me/theorems/736a1cb9-0287-48a8-a8af-810b06247db3
-- title:
--   Theorem 1, proof, final step: weak duality for the LP pair of Fig. 2
-- statement:
--   For an instance of the online ad-auctions problem, let $y$ be feasible for the packing LP of Fig. 2 and $(x, z)$ feasible for the covering LP. Then
--   $$
--   \sum_{j=1}^m \sum_{i\in I} b(i,j)\,y(i,j) \;\le\; \sum_{i\in I} B(i)\,x(i) + \sum_{j=1}^m z(j).
--   $$
--
--   This is the weak duality step that closes the proof of Theorem 1: the covering cost of the algorithm's run bounds the value of the fractional offline optimum.
-- source:
--   Buchbinder, Jain & Naor, Online Primal-Dual Algorithms for Maximizing Ad-Auctions Revenue, ESA 2007, DOI 10.1007/978-3-540-75520-3_24, p. 8, Theorem 1, proof, final sentence (weak duality)

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance

namespace BJNAdAuctions.Basic

/-- Theorem 1, proof, final step (p. 8): weak duality for the pair of LPs of Fig. 2. The value
of every feasible solution of the packing LP is at most the cost of every feasible solution of
the covering LP. -/
theorem weak_duality {I : Type*} [Fintype I] {m : ℕ} (inst : Instance I m)
    (y : I → Fin m → ℝ) (hy : PackingFeasible inst y)
    (x : I → ℝ) (z : Fin m → ℝ) (hxz : CoveringFeasible inst x z) :
    packingValue inst y ≤ coveringValue inst x z := by sorry

end BJNAdAuctions.Basic
