-- Prove2me | Theorems.Thm_ContPatrol_lemma_5
-- name    : ContPatrol.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:49.695862+00:00
-- url     : https://prove2.me/theorems/3f290dec-22ea-4b9d-9c8a-5c48676fb8b5
-- title:
--   Lemma 5 (corrected: at most): the independent attack on the leaves gives $V\le\alpha/(\mu+l\alpha/2)$
-- statement:
--   Let $Q$ be a network with total length $\mu$, $l\ge0$ leaf nodes and generalized girth $g^*$, and let $0<\alpha\le g^*$. Then the set of leaf nodes is independent, and by adopting the independent attack strategy on it the Attacker ensures that every patrol intercepts with probability at most $\alpha/(\mu+l\alpha/2)$. Hence
--   $$V\le\frac{\alpha}{\mu+l\alpha/2}.$$
--
--   This is the Attacker half of Theorem 6.
--
--   **Formalization Note** The paper says "less than"; the bound is attained (see below), so the statement says "at most".
--
--   Differences from the source:
--   - encoding: a network Q: a connected graph with positive arc lengths, viewed as a metric space; nodes are the points of degree ≠ 2; the line segment is excluded → MetricGraph V E with IsNetwork: finite types of vertices and edges, src/tgt maps (loops and parallel edges allowed), len e > 0, Nonempty E, connected, and (∃ v, 3 ≤ deg v) ∨ (∀ v, deg v ≠ 1); vertices of degree 2 allowed; points are vertices or interior points of edges; reason: a subdivided arc is the same metric space; every network arises this way, and leaf arcs, girth and reversals are defined subdivision-invariantly
--   - encoding: V, the value of the game (interception probability with best play on both sides) → lowerValue (sup of guarantees of measurable mixed patrols against pure attacks) and upperValue (inf of guarantees of mixed attacks against pure patrols); V ≤ v is upperValue ≤ v, V ≥ v is v ≤ lowerValue, V = v is both equalities; reason: the value, when it exists, is the common value of these two; existence (Garrec 2019) is not assumed
--   - encoding: mixed Patroller strategy → a family S ω of patrols on a probability space (Ω, P) with measurable evaluations ω ↦ S ω t; attacks are probability measures on (point, start time) with no mass on negative start times; reason: interception probabilities are then genuine probabilities; this is the standard meaning of a mixed strategy
--   - correction: the interception probability is less than α/(µ + lα/2) → at most α/(µ + lα/2); reason: counterexample: the star with three leaf arcs of length 1 and α = 1 ≤ g* = 2 has l = 3, µ = 3, λ(W^c) = 3/2, p = 2/3, and the patrol staying at one leaf forever intercepts with probability p/l = 2/9 = α/(µ + lα/2)
--   - generalization: the independent attack strategy on the set I of leaf nodes → also concludes that the leaf nodes form an independent set; reason: Definition 3 needs I independent; the proof gets it from Theorem 1 (p.8)
--   - generalization: standing assumption 0 < α < µ̄ (p.6) → 0 < α and α ≤ g* only; reason: α ≤ g* ≤ µ̄; the only extra case α = µ̄ is a circle with α = µ, where the bound is 1
--   - encoding: α ≤ g* → AlphaLeGenGirth: every circuit has length ≥ α and every leaf arc has length ≥ α/2; reason: g* = min(g, 2 · shortest leaf arc), with ∞ for an empty minimum
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Lemma 5, p.15

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_IsNetwork
import Definitions.Def_ContPatrol_MetricGraph_lowerValue
import Definitions.Def_ContPatrol_MetricGraph_AlphaLeGenGirth
import Definitions.Def_ContPatrol_MetricGraph_independentAttack

namespace ContPatrol

open MetricGraph

/-- **Lemma 5 (corrected: "less than" → "at most")** (Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Lemma 5,
p.15): "Suppose Q is a network with l ≥ 0 leaf nodes and generalized girth g∗. Then by adopting
the independent attack strategy on the set I of leaf nodes, the Attacker can ensure that the
interception probability is less than α/(µ+lα/2) for α ≤ g∗. Hence, V ≤ α/(µ + lα/2), for
α ≤ g∗."

For every network and every `α > 0` with `α ≤ g*`: the leaf nodes form an independent set, the
independent attack strategy on them holds every patrol to interception probability at most
`α/(µ + lα/2)`, and the upper value is at most `α/(µ + lα/2)`.

**Formalization Note.** "Less than" is corrected to "at most": on the star with three leaf arcs of
length 1 and `α = 1` (so `α ≤ g* = 2`), `l = 3`, `µ = 3`, `λ(W^c) = 3/2`, `p = 2/3`, and the
patrol that stays at one leaf forever intercepts with probability `p/l = 2/9 = α/(µ + lα/2)`.
The standing assumption `α < µ̄` is not assumed. -/
theorem lemma_5 {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MetricGraph V E) (hG : G.IsNetwork) (α : ℝ) (hα : 0 < α) (hg : G.AlphaLeGenGirth α) :
    G.IsIndependent α G.leafPoints ∧
      G.AttackGuarantee α (G.independentAttack α G.leafPoints)
        (α / (G.totalLength + G.leafCount * α / 2)) ∧
      G.upperValue α ≤ α / (G.totalLength + G.leafCount * α / 2) := by sorry

end ContPatrol
