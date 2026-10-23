-- Prove2me | Theorems.Thm_ContingentSourcing_Competition_lemma_1
-- name    : ContingentSourcing.Competition.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:01.756998+00:00
-- url     : https://prove2.me/theorems/eb94f0a1-b824-4c9d-9d5f-a444d4503c3d
-- title:
--   Lemma 1, p. 12 — for w_R ≤ w_E some optimal order has no emergency order after a good signal
-- statement:
--   Consider the buyer's two-stage sourcing problem (2) with market potential $m$, delivery probability $P_1$ of supplier U, signal accuracy $\rho\in[0,1]$, and wholesale prices $w_U$ (supplier U), $w_R$ (supplier R, Time 0) and $w_E$ (supplier R, emergency order at Time 1).
--
--   If $w_R\le w_E$, then the buyer's problem has an optimal solution $(Q_U^*,Q_R^*,Q_E^*(G),Q_E^*(B))$, all components nonnegative, with
--   $$Q_E^*(G)=0 .$$
--
--   Thus without loss of optimality the buyer never places an emergency order after a good signal, and the emergency order is written $Q_E=Q_E(B)$ from then on.
--
--   **Formalization Note.** The prices $w_U$ and $w_R$ are assumed nonnegative and $0\le\rho\le1$; the paper uses nonnegative prices throughout its proofs, and with $w_U<0$ the objective (2) is unbounded so that no optimal solution exists. "Optimal" means feasible and maximizing (2) over all feasible orders.
-- source:
--   Lu & Tomlin, Forewarned Is Forearmed?, SSRN 4260604 author manuscript (1 May 2023) of MSOM doi:10.1287/msom.2021.0540, p. 12 (PDF 12), Lemma 1

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

namespace ContingentSourcing.Competition

/-- Lemma 1, p. 12: for any w_R ≤ w_E there is an optimal solution of the buyer's problem (2) with
Q*_E(G) = 0 (and Q*_E(B) ≥ 0, part of feasibility). Nonnegative prices and 0 ≤ ρ ≤ 1 are added. -/
theorem lemma_1 (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (w : Prices) (hwU : 0 ≤ w.wU) (hwR : 0 ≤ w.wR) (hRE : w.wR ≤ w.wE) :
    ∃ q : Orders, P.IsOptimalOrder ρ w q ∧ q.QEG = 0 := by sorry

end ContingentSourcing.Competition
