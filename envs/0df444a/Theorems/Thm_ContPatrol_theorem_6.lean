-- Prove2me | Theorems.Thm_ContPatrol_theorem_6
-- name    : ContPatrol.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:23.471246+00:00
-- url     : https://prove2.me/theorems/734ac76c-e3db-4f0b-8124-ff8b2195214a
-- title:
--   Theorem 6: for $\alpha\le g^*$, $V=\alpha/(\mu+l\alpha/2)$, attained by $S_2^\alpha$ and the independent attack on the leaves
-- statement:
--   Let $Q$ be a network (finite, connected, not a line segment; loops, parallel arcs and subdivided arcs allowed) with total length $\mu$, $l\ge0$ leaf nodes and generalized girth $g^*$, and let $0<\alpha\le g^*$. Then
--   $$V=\frac{\alpha}{\mu+l\alpha/2}.$$
--
--   1. **Patroller.** For every double tour $S_2$ of Theorem 3, the randomized periodic extension of the leaf-pausing tour $S_2^\alpha$ intercepts every attack with probability at least $\alpha/(\mu+l\alpha/2)$; it is optimal.
--   2. **Attacker.** The leaf nodes form an independent set, and the independent attack strategy on it holds every patrol to interception probability at most $\alpha/(\mu+l\alpha/2)$; it is optimal.
--
--   Since $g^*>0$ on every network, this solves the continuous patrolling game for all sufficiently short attacks on any network.
--
--   **Formalization Note** "$V=v$" is the conjunction lower value $=v$ and upper value $=v$; the existence of the value is concluded, not assumed.
--
--   Differences from the source:
--   - encoding: a network Q: a connected graph with positive arc lengths, viewed as a metric space; nodes are the points of degree ≠ 2; the line segment is excluded → MetricGraph V E with IsNetwork: finite types of vertices and edges, src/tgt maps (loops and parallel edges allowed), len e > 0, Nonempty E, connected, and (∃ v, 3 ≤ deg v) ∨ (∀ v, deg v ≠ 1); vertices of degree 2 allowed; points are vertices or interior points of edges; reason: a subdivided arc is the same metric space; every network arises this way, and leaf arcs, girth and reversals are defined subdivision-invariantly
--   - encoding: V, the value of the game (interception probability with best play on both sides) → lowerValue (sup of guarantees of measurable mixed patrols against pure attacks) and upperValue (inf of guarantees of mixed attacks against pure patrols); V ≤ v is upperValue ≤ v, V ≥ v is v ≤ lowerValue, V = v is both equalities; reason: the value, when it exists, is the common value of these two; existence (Garrec 2019) is not assumed
--   - encoding: mixed Patroller strategy → a family S ω of patrols on a probability space (Ω, P) with measurable evaluations ω ↦ S ω t; attacks are probability measures on (point, start time) with no mass on negative start times; reason: interception probabilities are then genuine probabilities; this is the standard meaning of a mixed strategy
--   - generalization: standing assumption 0 < α < µ̄ (p.6) → 0 < α and α ≤ g* only; reason: α ≤ g* ≤ µ̄, and α = g* = µ̄ happens only for a circle with α = µ, where V = 1 = α/µ = α/(µ + lα/2)
--   - encoding: α ≤ g* → AlphaLeGenGirth: every circuit has length ≥ α and every leaf arc has length ≥ α/2; reason: g* = min(g, 2 · shortest leaf arc), with ∞ for an empty minimum
--   - encoding: an optimal strategy is S2^α / the independent attack strategy → each guarantees α/(µ + lα/2), which equals both the lower and the upper value; reason: optimality of a strategy means it guarantees the value
--   - generalization: S2^α for a tour S2 given by Theorem 3 → for every closed dart walk d :: ds with IsDoubleTour; reason: Definition 5 takes any tour of Theorem 3; stating it for all of them includes the source's
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Theorem 6, p.15

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_IsNetwork
import Definitions.Def_ContPatrol_MetricGraph_lowerValue
import Definitions.Def_ContPatrol_MetricGraph_AlphaLeGenGirth
import Definitions.Def_ContPatrol_MetricGraph_independentAttack
import Definitions.Def_ContPatrol_MetricGraph_periodicExt
import Definitions.Def_ContPatrol_Multigraph_IsDoubleTour
import Definitions.Def_ContPatrol_MetricGraph_pausedTour

namespace ContPatrol

open MetricGraph

/-- **Theorem 6** (Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Theorem 6, p.15):
"If Q is a network with l ≥ 0 leaf nodes and generalized girth g∗, then V = α/(µ + lα/2), for
α ≤ g∗. For the Patroller, an optimal strategy is S2^α as defined above. For the Attacker, an
optimal strategy is the independent attack strategy, taking I to be the independent set of leaf
nodes."

For every network Q (finite, connected, not a line segment; loops, parallel edges and vertices of
degree 2 allowed) with `l ≥ 0` leaf nodes and total length `µ`, and every `α > 0` with `α ≤ g*`,
writing `v = α/(µ + lα/2)`:
1. the lower and the upper value of the game both equal `v`;
2. for every double tour `S₂ = d :: ds` of Theorem 3, the randomized periodic extension of the
   leaf-pausing tour `S₂^α` guarantees interception probability `v` against every attack;
3. the leaf nodes form an independent set, and the independent attack strategy on them holds every
   patrol to interception probability at most `v`.

**Formalization Note.** "V = v" is `lowerValue = v ∧ upperValue = v`; existence of the value is
not assumed but concluded. The paper's standing assumption `α < µ̄` (p.6) is not assumed: under
`α ≤ g*` it excludes only `α = µ̄`, which happens only for a circle with `α = µ`, where `V = 1 = v`. -/
theorem theorem_6 {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MetricGraph V E) (hG : G.IsNetwork) (α : ℝ) (hα : 0 < α) (hg : G.AlphaLeGenGirth α) :
    G.lowerValue α = α / (G.totalLength + G.leafCount * α / 2) ∧
      G.upperValue α = α / (G.totalLength + G.leafCount * α / 2) ∧
      (∀ (d : E × Bool) (ds : List (E × Bool)), G.IsDoubleTour (d :: ds) →
        G.PatrolGuarantee α (shiftLaw (G.pausedPeriod α (d :: ds)))
          (periodicExt (G.pausedTour α d ds) (G.pausedPeriod α (d :: ds)))
          (α / (G.totalLength + G.leafCount * α / 2))) ∧
      G.IsIndependent α G.leafPoints ∧
      G.AttackGuarantee α (G.independentAttack α G.leafPoints)
        (α / (G.totalLength + G.leafCount * α / 2)) := by sorry

end ContPatrol
