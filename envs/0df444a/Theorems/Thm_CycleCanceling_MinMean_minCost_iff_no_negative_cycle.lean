-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_minCost_iff_no_negative_cycle
-- name    : CycleCanceling.MinMean.minCost_iff_no_negative_cycle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:11:47.679647+00:00
-- url     : https://prove2.me/theorems/ca456bb5-2980-40bb-b2ec-7c0a2ce1d52a
-- title:
--   Theorem 2.1 — a circulation is minimum-cost iff it has no negative residual cycle
-- statement:
--   Let $G=(V,E)$ be a circulation network with capacities $u$ and antisymmetric costs $c$, and let $f$ be a circulation. Then
--   $$
--   f \text{ is minimum-cost}\iff \text{there is no residual cycle }\Gamma\text{ of }f\text{ with } c(\Gamma)<0 .
--   $$
--   This classical criterion (Busacker and Saaty) is what the cycle-canceling algorithm rests on: the algorithm stops exactly at an optimal circulation.
--
--   **Formalization Note** Residual cycles are simple cycles given by duplicate-free vertex lists; one- and two-vertex cycles are included, and have cost $0$.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, p. 876, Theorem 2.1

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network

namespace CycleCanceling.MinMean

/-- Theorem 2.1 (Goldberg–Tarjan 1989, p. 876): a circulation is minimum-cost if and only if
there are no negative residual cycles. -/
theorem minCost_iff_no_negative_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f) :
    IsMinCost N f ↔ ¬ ∃ Γ : List V, IsResidualCycle N f Γ ∧ cycleCost N Γ < 0 := by sorry

end CycleCanceling.MinMean
