-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_Supplement_lemma_3_8
-- name    : ApproxEquilibriumCost.General.Supplement.lemma_3_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:46:30.615852+00:00
-- url     : https://prove2.me/theorems/5e3af4ce-171d-4721-a54f-8166a338e5a8
-- title:
--   Lemma 3.8 (used in the proof of Theorem 3.10) — every-path latency lower bound
-- statement:
--   Let $G$ be a single-commodity routing game on an arbitrary series-parallel network $N$ of depth $h_N$, with arbitrary demand $r>0$ and continuous, nonnegative, nondecreasing latencies. Let $f$ be a Nash flow, $\epsilon\ge0$, and $f'$ an $\epsilon$-equilibrium for the same demand. For every path $P$ used by $f$ and every terminal path $Q$,
--
--   $$\ell_Q(f')\ge\frac{\ell_P(f)}{1+h_N\epsilon}=\frac{L_G}{1+h_N\epsilon}.$$
--
--   The assertion includes paths unused by $f'$ and permits zero Nash cost. It is the path-latency support for Theorem 3.10.
--
--   Differences from the source:
--   - encoding: single-commodity routing on an arbitrary series-parallel network → an arbitrary recursive SPNetwork term N and a published Game N.edgeCount 1 whose strategies equal N.paths; reason: the three constructors generate exactly the source networks, with distinct Fin-labelled edges and all terminal paths; arbitrary positive real demand is already a Game field
--   - encoding: latencies on the nonnegative reals → total real functions constrained to be continuous, nonnegative and nondecreasing on [0,∞); reason: only nonnegative feasible loads are evaluated, so negative-argument values change no instance
--   - encoding: L_G is the common latency of the paths used by f → strategyLatency G f P for every allowed route P with 0 < f P; reason: positive demand and feasibility give a used route, and Nash equilibrium makes every such latency equal to L_G
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Lemma 3.8, printed p.14 = PDF p.14 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_RoutingGame

namespace ApproxEquilibriumCost.General.Supplement

/-- Lemma 3.8, printed/PDF p.14; proof p.28. Every path is bounded,
including paths unused by the approximate equilibrium. -/
theorem lemma_3_8 (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (ε : ℝ) (hε : 0 ≤ ε) (f' : Flow G) (hf' : IsApproxNash G ε f')
    (P Q : Fin (routeCount G)) (hP : 0 < f P) :
    strategyLatency G f P / (1 + (depth N : ℝ) * ε) ≤
      strategyLatency G f' Q := by sorry

end ApproxEquilibriumCost.General.Supplement
