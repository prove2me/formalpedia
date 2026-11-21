-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_Supplement_lemma_B_1
-- name    : ApproxEquilibriumCost.General.Supplement.lemma_B_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:48:43.600936+00:00
-- url     : https://prove2.me/theorems/20d95235-e261-4b72-ab23-ac6093cdeef9
-- title:
--   Lemma B.1 (used in the proof of Theorem B.2) — some-path latency upper bound
-- statement:
--   Let $G$ be a single-commodity routing game on any series-parallel network, with arbitrary demand $r>0$ and continuous, nonnegative, nondecreasing latencies. Let $f$ be a Nash flow and $f'$ any feasible flow for the same demand. For every path $P$ used by $f$, there exists a terminal path $Q$ such that
--
--   $$\ell_Q(f')\le\ell_P(f)=L_G.$$
--
--   No equilibrium condition is imposed on $f'$, and no positivity of $C(f)$ is required. The path found here supports Theorem B.2.
--
--   Differences from the source:
--   - encoding: single-commodity routing on an arbitrary series-parallel network → an arbitrary recursive SPNetwork term N and a published Game N.edgeCount 1 whose strategies equal N.paths; reason: the three constructors generate exactly the source networks, with distinct Fin-labelled edges and all terminal paths; arbitrary positive real demand is already a Game field
--   - encoding: latencies on the nonnegative reals → total real functions constrained to be continuous, nonnegative and nondecreasing on [0,∞); reason: only nonnegative feasible loads are evaluated, so negative-argument values change no instance
--   - encoding: L_G is the common latency of the paths used by f → strategyLatency G f P for every allowed route P with 0 < f P; reason: positive demand and feasibility give a used route, and Nash equilibrium makes every such latency equal to L_G
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Lemma B.1, printed p.28 = PDF p.28 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_RoutingGame

namespace ApproxEquilibriumCost.General.Supplement

/-- Lemma B.1, printed/PDF p.28; proof p.29. The second flow is
any feasible flow with the same demand, without equilibrium requirements. -/
theorem lemma_B_1 (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (f' : Flow G) (hf' : IsFeasible G f')
    (P : Fin (routeCount G)) (hP : 0 < f P) :
    ∃ Q : Fin (routeCount G), strategyLatency G f' Q ≤ strategyLatency G f P := by sorry

end ApproxEquilibriumCost.General.Supplement
