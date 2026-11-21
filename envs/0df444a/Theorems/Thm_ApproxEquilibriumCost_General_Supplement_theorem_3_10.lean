-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_Supplement_theorem_3_10
-- name    : ApproxEquilibriumCost.General.Supplement.theorem_3_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:46:53.977492+00:00
-- url     : https://prove2.me/theorems/c6100b80-6353-443e-a5f8-fc10668a3172
-- title:
--   Theorem 3.10 (companion theorem; not used in the proof of the goal) — depth-dependent cost lower bound
-- statement:
--   Consider a single-commodity routing game on any series-parallel network $N$ of depth $h_N$, with arbitrary real demand $r>0$ and continuous, nonnegative, nondecreasing latencies. Let $f$ be a Nash flow with $C(f)>0$. For every real $\epsilon\ge0$ and every $\epsilon$-equilibrium $f'$ for the same game,
--
--   $$\frac{C(f')}{C(f)}\ge\frac{1}{1+h_N\epsilon}.$$
--
--   This companion theorem bounds cost reductions for general monotone latencies. It is independent of the proof of the retained goal Corollary 3.3.
--
--   Differences from the source:
--   - encoding: single-commodity routing on an arbitrary series-parallel network → an arbitrary recursive SPNetwork term N and a published Game N.edgeCount 1 whose strategies equal N.paths; reason: the three constructors generate exactly the source networks, with distinct Fin-labelled edges and all terminal paths; arbitrary positive real demand is already a Game field
--   - encoding: latencies on the nonnegative reals → total real functions constrained to be continuous, nonnegative and nondecreasing on [0,∞); reason: only nonnegative feasible loads are evaluated, so negative-argument values change no instance
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Theorem 3.10, printed p.16 = PDF p.16 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_RoutingGame

namespace ApproxEquilibriumCost.General.Supplement

/-- Theorem 3.10, printed/PDF p.16. Arbitrary positive real demand
and continuous nonnegative nondecreasing latencies, of any shape. -/
theorem theorem_3_10 (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (hcost : 0 < cost G f) (ε : ℝ) (hε : 0 ≤ ε)
    (f' : Flow G) (hf' : IsApproxNash G ε f') :
    1 / (1 + (depth N : ℝ) * ε) ≤ cost G f' / cost G f := by sorry

end ApproxEquilibriumCost.General.Supplement
