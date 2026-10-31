-- Prove2me | Theorems.Thm_ContPatrol_lemma_4
-- name    : ContPatrol.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:33.574802+00:00
-- url     : https://prove2.me/theorems/92db607e-1c15-4726-8a25-7702779ae23d
-- title:
--   Lemma 4: $V\ge\alpha/(\mu+l\alpha/2)$ for $\alpha\le g$
-- statement:
--   Let $Q$ be a network with total length $\mu$, $l\ge0$ leaf nodes and girth $g$, and let $0<\alpha\le g$. Then
--   $$V\ge\frac{\alpha}{\mu+l\alpha/2}.$$
--   Moreover, for every double tour $S_2$ of Theorem 3, the randomized periodic extension of the leaf-pausing tour $S_2^\alpha$ guarantees interception probability $\alpha/(\mu+l\alpha/2)$ against every attack.
--
--   This is the Patroller half of Theorem 6.
--
--   **Formalization Note** The second sentence is the strategy constructed in the proof ($2\alpha/(2\mu+l\alpha)=\alpha/(\mu+l\alpha/2)$); with Theorem 3 it implies the first.
--
--   Differences from the source:
--   - encoding: a network Q: a connected graph with positive arc lengths, viewed as a metric space; nodes are the points of degree ≠ 2; the line segment is excluded → MetricGraph V E with IsNetwork: finite types of vertices and edges, src/tgt maps (loops and parallel edges allowed), len e > 0, Nonempty E, connected, and (∃ v, 3 ≤ deg v) ∨ (∀ v, deg v ≠ 1); vertices of degree 2 allowed; points are vertices or interior points of edges; reason: a subdivided arc is the same metric space; every network arises this way, and leaf arcs, girth and reversals are defined subdivision-invariantly
--   - encoding: V, the value of the game (interception probability with best play on both sides) → lowerValue (sup of guarantees of measurable mixed patrols against pure attacks) and upperValue (inf of guarantees of mixed attacks against pure patrols); V ≤ v is upperValue ≤ v, V ≥ v is v ≤ lowerValue, V = v is both equalities; reason: the value, when it exists, is the common value of these two; existence (Garrec 2019) is not assumed
--   - encoding: mixed Patroller strategy → a family S ω of patrols on a probability space (Ω, P) with measurable evaluations ω ↦ S ω t; attacks are probability measures on (point, start time) with no mass on negative start times; reason: interception probabilities are then genuine probabilities; this is the standard meaning of a mixed strategy
--   - generalization: standing assumption 0 < α < µ̄ (p.6) → 0 < α and α ≤ g only; reason: α ≤ g ≤ µ̄; the only extra case α = µ̄ is a circle with α = µ, where the bound α/µ = 1 holds (going round the circle intercepts every attack)
--   - generalization: V ≥ α/(µ + lα/2) → also: for every double tour S₂ the randomized periodic extension of S₂^α guarantees α/(µ + lα/2); reason: the strategy of the proof; it implies the printed bound through Theorem 3
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Lemma 4, p.14 (proof p.15)

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_IsNetwork
import Definitions.Def_ContPatrol_MetricGraph_lowerValue
import Definitions.Def_ContPatrol_MetricGraph_leafArcLength
import Definitions.Def_ContPatrol_MetricGraph_lengthMeasure
import Definitions.Def_ContPatrol_MetricGraph_AlphaLeGirth
import Definitions.Def_ContPatrol_MetricGraph_periodicExt
import Definitions.Def_ContPatrol_Multigraph_IsDoubleTour
import Definitions.Def_ContPatrol_MetricGraph_pausedTour

namespace ContPatrol

open MetricGraph

/-- **Lemma 4** (Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Lemma 4, p.14; proof p.15):
"Suppose Q is a network with l ≥ 0 leaf nodes and girth g. Then V ≥ α/(µ + lα/2), for α ≤ g."

For every network and every `α > 0` with `α ≤ g`: the lower value is at least `α/(µ + lα/2)`; and,
as the proof shows, for every double tour `S₂ = d :: ds` of Theorem 3 the randomized periodic
extension of the leaf-pausing tour `S₂^α` (period `L`) guarantees interception probability
`α/(µ + lα/2)` against every attack.

**Formalization Note.** The second conjunct is the Patroller strategy of the proof
(`2α/(2µ + lα) = α/(µ + lα/2)`); it implies the first through Theorem 3. The standing assumption
`α < µ̄` is not assumed. -/
theorem lemma_4 {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MetricGraph V E) (hG : G.IsNetwork) (α : ℝ) (hα : 0 < α) (hg : G.AlphaLeGirth α) :
    α / (G.totalLength + G.leafCount * α / 2) ≤ G.lowerValue α ∧
      ∀ (d : E × Bool) (ds : List (E × Bool)), G.IsDoubleTour (d :: ds) →
        G.PatrolGuarantee α (shiftLaw (G.pausedPeriod α (d :: ds)))
          (periodicExt (G.pausedTour α d ds) (G.pausedPeriod α (d :: ds)))
          (α / (G.totalLength + G.leafCount * α / 2)) := by sorry

end ContPatrol
