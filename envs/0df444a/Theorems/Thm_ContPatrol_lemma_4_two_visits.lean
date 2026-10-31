-- Prove2me | Theorems.Thm_ContPatrol_lemma_4_two_visits
-- name    : ContPatrol.lemma_4_two_visits
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:57.124395+00:00
-- url     : https://prove2.me/theorems/68d93c8d-110c-499f-960d-a00f3d934bf0
-- title:
--   Proof of Lemma 4: $S_2^\alpha$ has period $2\mu+l\alpha$ and visits every point twice, $\alpha$ apart
-- statement:
--   Let $Q$ be a network with total length $\mu$ and $l\ge0$ leaf nodes, let $\alpha>0$ with $\alpha\le g$ (every circuit has length at least $\alpha$), and let $S_2$ be a double tour of Theorem 3. Then:
--
--   1. the leaf-pausing tour $S_2^\alpha$ takes total time
--   $$L=2\mu+l\alpha;$$
--   2. $S_2^\alpha$ is a closed unit speed path of period $L$;
--   3. every point of $Q$ is visited by $S_2^\alpha$ at two times in $[0,L)$ that are at least $\alpha$ apart in both directions around the period.
--
--   This is exactly the hypothesis of Theorem 2 with $k=2$, which yields Lemma 4.
--
--   **Formalization Note** Only $\alpha\le g$ is assumed, as in Lemma 4; the leaf-arc half of $g^*$ is not needed.
--
--   Differences from the source:
--   - encoding: a network Q: a connected graph with positive arc lengths, viewed as a metric space; nodes are the points of degree ≠ 2; the line segment is excluded → MetricGraph V E with IsNetwork: finite types of vertices and edges, src/tgt maps (loops and parallel edges allowed), len e > 0, Nonempty E, connected, and (∃ v, 3 ≤ deg v) ∨ (∀ v, deg v ≠ 1); vertices of degree 2 allowed; points are vertices or interior points of edges; reason: a subdivided arc is the same metric space; every network arises this way, and leaf arcs, girth and reversals are defined subdivision-invariantly
--   - encoding: every point of Q is visited by S2^α at two times differing by at least α → VisitsSeparated (S₂^α) L α 2: two visit times in [0, L) with both cyclic gaps ≥ α, and α ≤ L; reason: this is the hypothesis of Theorem 2 with k = 2 to which the proof applies the claim (same reading as Theorem 2)
--   - generalization: Tour S2^α takes total time 2µ + lα; every point visited twice → also concludes that S₂^α is a closed unit speed path of period L; reason: implicit in calling S₂^α a tour and applying Theorem 2; the two printed claims are the other conjuncts
--   - generalization: standing assumption 0 < α < µ̄ (p.6) → 0 < α and α ≤ g only; reason: α ≤ g ≤ µ ≤ µ̄; the only extra case α = µ̄ is a circle with α = µ, where the claim holds
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, proof of Lemma 4, p.15

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_IsNetwork
import Definitions.Def_ContPatrol_MetricGraph_lengthMeasure
import Definitions.Def_ContPatrol_MetricGraph_leafArcLength
import Definitions.Def_ContPatrol_MetricGraph_AlphaLeGirth
import Definitions.Def_ContPatrol_MetricGraph_periodicExt
import Definitions.Def_ContPatrol_Multigraph_IsDoubleTour
import Definitions.Def_ContPatrol_MetricGraph_pausedTour

namespace ContPatrol

open MetricGraph

/-- **The two-visit property of S₂^α** (Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, proof of Lemma 4,
p.15): "Tour S2^α takes total time 2µ + lα. Note that every point of Q is visited by S2^α at two
times differing by at least α. So by Theorem 2 part (i) with k = 2, L = 2µ + lα, we have
V ≥ 2α/(2µ + lα)."

For every network, every `α > 0` with `α ≤ g` (every circuit has length at least `α`), and every
double tour `S₂ = d :: ds` of Theorem 3: the leaf-pausing tour `S₂^α` has period
`L = 2µ + lα`, it is a closed unit speed path of period `L`, and it visits every point of Q at two
times that are at least `α` apart cyclically (the hypothesis of Theorem 2 with `k = 2`).

**Formalization Note.** The proof's two claims about `S₂^α` (its period and the two visits) are
stated together with the fact, implicit in calling `S₂^α` a tour and applying Theorem 2, that it is
a closed unit speed path. Only `α ≤ g` is assumed: the leaf-arc part of `g*` is not needed here
(Lemma 4 assumes only `α ≤ g`). -/
theorem lemma_4_two_visits {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MetricGraph V E) (hG : G.IsNetwork) (α : ℝ) (hα : 0 < α) (hg : G.AlphaLeGirth α)
    (d : E × Bool) (ds : List (E × Bool)) (hw : G.IsDoubleTour (d :: ds)) :
    G.pausedPeriod α (d :: ds) = 2 * G.totalLength + G.leafCount * α ∧
      G.IsClosedUnitSpeedPath (G.pausedTour α d ds) (G.pausedPeriod α (d :: ds)) ∧
      G.VisitsSeparated (G.pausedTour α d ds) (G.pausedPeriod α (d :: ds)) α 2 := by sorry

end ContPatrol
