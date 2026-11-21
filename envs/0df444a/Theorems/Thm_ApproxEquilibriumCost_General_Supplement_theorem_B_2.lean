-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_Supplement_theorem_B_2
-- name    : ApproxEquilibriumCost.General.Supplement.theorem_B_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:49:25.667426+00:00
-- url     : https://prove2.me/theorems/cb68c25a-986c-4d9c-aadc-61c9bc98a638
-- title:
--   Theorem B.2 (companion theorem; not used in the proof of the goal) — series-parallel cost upper bound
-- statement:
--   Consider any single-commodity routing game on a series-parallel network, with arbitrary positive real demand and continuous, nonnegative, nondecreasing latencies. Let $f$ be a Nash flow with $C(f)>0$. For every real $\epsilon\ge0$ and every $\epsilon$-equilibrium $f'$ for the same game,
--
--   $$\frac{C(f')}{C(f)}\le1+\epsilon.$$
--
--   The theorem has no depth restriction and no polynomial hypothesis. It is the companion upper bound attributed to Kleer–Schäfer in the source and proved there using Lemma B.1; it is independent of the retained goal's proof.
--
--   Differences from the source:
--   - encoding: single-commodity routing on an arbitrary series-parallel network → an arbitrary recursive SPNetwork term N and a published Game N.edgeCount 1 whose strategies equal N.paths; reason: the three constructors generate exactly the source networks, with distinct Fin-labelled edges and all terminal paths; arbitrary positive real demand is already a Game field
--   - encoding: latencies on the nonnegative reals → total real functions constrained to be continuous, nonnegative and nondecreasing on [0,∞); reason: only nonnegative feasible loads are evaluated, so negative-argument values change no instance
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Theorem B.2, printed p.29 = PDF p.29 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_RoutingGame

namespace ApproxEquilibriumCost.General.Supplement

/-- Theorem B.2, printed/PDF p.29, attributed there to Kleer–Schäfer.
No depth bound or polynomial hypothesis is imposed. -/
theorem theorem_B_2 (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (hcost : 0 < cost G f) (ε : ℝ) (hε : 0 ≤ ε)
    (f' : Flow G) (hf' : IsApproxNash G ε f') :
    cost G f' / cost G f ≤ 1 + ε := by sorry

end ApproxEquilibriumCost.General.Supplement
