-- Prove2me | Theorems.Thm_CostlySeeding_EdgeQuery_submodular
-- name    : CostlySeeding.EdgeQuery.submodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:01.758994+00:00
-- url     : https://prove2.me/theorems/8b7f9e4b-5d55-4326-a0b8-929b2195fd71
-- title:
--   §3.3, p. 17 — truncated-sketch coverage is monotone submodular
-- statement:
--   For any fixed output of PROBE with positive sampling rate $\rho$, a positive number $T$ of copies and positive truncation threshold $\tau$, the truncated-sketch objective $\Gamma^{(T)}_{\rho,\tau}$ is a monotone submodular function of the seed set. In particular, for seed sets $S\subseteq U$ and arbitrary seed sets $A,B$,
--
--   $$
--   \Gamma^{(T)}_{\rho,\tau}(S)\le\Gamma^{(T)}_{\rho,\tau}(U),\qquad
--   \Gamma^{(T)}_{\rho,\tau}(A\cup B)+\Gamma^{(T)}_{\rho,\tau}(A\cap B)\le\Gamma^{(T)}_{\rho,\tau}(A)+\Gamma^{(T)}_{\rho,\tau}(B).
--   $$
--
--   These are the structural properties needed for the stochastic-greedy approximation guarantee.
--
--   **Formalization Note** The page explicitly states submodularity; monotonicity is included because the same coverage representation gives it.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, p. 17, §3.3 paragraph before Lemma 4

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

namespace CostlySeeding.EdgeQuery

theorem submodular (n T tau : ℕ) (hT : 0 < T) (htau : 0 < tau)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (rho : ℝ) (hrho : 0 < rho)
    (ss : Fin T → ProbeSeed n) :
    MonotoneSet (GamCut G Vrho rho tau ss) ∧
      SubmodularSet (GamCut G Vrho rho tau ss) := by sorry

end CostlySeeding.EdgeQuery
