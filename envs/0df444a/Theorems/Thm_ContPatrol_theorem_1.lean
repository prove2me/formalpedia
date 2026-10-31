-- Prove2me | Theorems.Thm_ContPatrol_theorem_1
-- name    : ContPatrol.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:10.105205+00:00
-- url     : https://prove2.me/theorems/e3601726-669d-4850-86bd-abcfe2d8bded
-- title:
--   Theorem 1: the independent attack strategy gives $V\le\alpha/(\lambda(W^c)+l\alpha)$
-- statement:
--   Let $Q$ be a network of total length $\mu$ and $\alpha>0$.
--
--   1. If $I$ is an independent set of cardinality $l$ and $W=W(I)$, then the independent attack strategy holds every patrol to interception probability at most
--   $$\frac{\alpha}{\lambda(W^c)+l\alpha},$$
--   and hence $V\le\alpha/(\lambda(W^c)+l\alpha)$.
--   2. If moreover $\lambda(W^c)=0$, then $l\ge1$ and $V\le1/l$.
--   3. If every leaf arc has length at least $\alpha/2$, then the set of leaf nodes is independent, $\lambda(W^c)=\mu-l\alpha/2$ for it, and
--   $$V\le\frac{\alpha}{\mu+l\alpha/2}.$$
--
--   Clause 3 is the Attacker half of the solution on networks with leaves (Lemma 5, Theorem 6).
--
--   **Formalization Note** In clause 3 the paper says "exceeding $\alpha/2$"; the statement is made with "at least $\alpha/2$", which includes the paper's case and is the form used by Lemma 5. It also records the two facts of the proof, independence of the leaf nodes and $\lambda(W)=l\alpha/2$.
--
--   Differences from the source:
--   - encoding: a network Q: a connected graph with positive arc lengths, viewed as a metric space; nodes are the points of degree ≠ 2; the line segment is excluded → MetricGraph V E with IsNetwork: finite types of vertices and edges, src/tgt maps (loops and parallel edges allowed), len e > 0, Nonempty E, connected, and (∃ v, 3 ≤ deg v) ∨ (∀ v, deg v ≠ 1); vertices of degree 2 allowed; points are vertices or interior points of edges; reason: a subdivided arc is the same metric space; every network arises this way, and leaf arcs, girth and reversals are defined subdivision-invariantly
--   - encoding: V, the value of the game (interception probability with best play on both sides) → lowerValue (sup of guarantees of measurable mixed patrols against pure attacks) and upperValue (inf of guarantees of mixed attacks against pure patrols); V ≤ v is upperValue ≤ v, V ≥ v is v ≤ lowerValue, V = v is both equalities; reason: the value, when it exists, is the common value of these two; existence (Garrec 2019) is not assumed
--   - encoding: mixed Patroller strategy → a family S ω of patrols on a probability space (Ω, P) with measurable evaluations ω ↦ S ω t; attacks are probability measures on (point, start time) with no mass on negative start times; reason: interception probabilities are then genuine probabilities; this is the standard meaning of a mixed strategy
--   - generalization: standing assumption 0 < α < µ̄ (p.6) → 0 < α only; reason: for α ≥ µ̄ every bound is ≥ 1 and so trivially true: two points of Q are at distance ≤ µ̄/2, so an independent set has l ≤ 1, and l = 1 forces W = Q; the Lean range contains the source's
--   - encoding: an independent subset I of Q of cardinality l → I : Finset of points with IsIndependent α I, l = I.card; reason: with α > 0 every independent subset of the compact network Q is finite
--   - generalization: If λ(W^c) = 0 we have V ≤ 1/l → λ(W^c) = 0 → 0 < l ∧ upperValue ≤ 1/l; reason: l ≥ 1 is an extra conclusion (λ(W(∅)^c) = µ > 0), stated so that 1/l is never Lean's 1/0 = 0
--   - generalization: leaf arcs have lengths exceeding α/2 → every leaf arc has length at least α/2; reason: the weaker hypothesis covers the source's case; Lemma 5 uses this form ("all leaf arcs have length at least α/2", p.15)
--   - generalization: conclusion V ≤ α/(µ + lα/2) for the leaf set → also concludes that the leaf nodes are independent and λ(W^c) = µ − lα/2; reason: the two facts stated in the proof (p.8); the printed bound is the third conjunct
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Theorem 1, p.7 (proof pp.7–8)

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_IsNetwork
import Definitions.Def_ContPatrol_MetricGraph_lowerValue
import Definitions.Def_ContPatrol_MetricGraph_leafArcLength
import Definitions.Def_ContPatrol_MetricGraph_independentAttack

namespace ContPatrol

open MetricGraph

/-- **Theorem 1** (Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Theorem 1, p.7; proof pp.7–8):
"Suppose I is an independent subset of Q of cardinality l. Then V ≤ α/(λ(W^c) + lα), which the
Attacker can ensure by adopting the independent attack strategy. If λ(W^c) = 0 we have V ≤ 1/l.
Furthermore, if I is the set of leaf nodes, and leaf arcs have lengths exceeding α/2, then
V ≤ α/(µ + lα/2)."

For every network and every `α > 0`:
1. for every independent finite set `I` of cardinality `l`, with `W = W(I)`, the independent
   attack strategy holds every patrol to interception probability at most `α/(λ(W^c) + lα)`, and
   the upper value is at most that;
2. if moreover `λ(W^c) = 0`, then `l ≥ 1` and the upper value is at most `1/l`;
3. if every leaf arc has length at least `α/2`, then the set of leaf nodes is independent,
   `λ(W^c) = µ − lα/2` for it, and the upper value is at most `α/(µ + lα/2)`.

**Formalization Note.** In clause 3 the paper's "exceeding α/2" is relaxed to "at least α/2"
(the form Lemma 5 uses, p.15); clause 3 also records the two facts its proof states
("leaf nodes form an independent set I and λ(W) = lα/2"). In clause 2, `l ≥ 1` is a conclusion
(`λ(W(∅)^c) = µ > 0`), so `1/l` is never `1/0`. The standing assumption `α < µ̄` is not assumed. -/
theorem theorem_1 {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MetricGraph V E) (hG : G.IsNetwork) (α : ℝ) (hα : 0 < α) :
    (∀ I : Finset G.Point, G.IsIndependent α I →
      G.AttackGuarantee α (G.independentAttack α I)
          (α / ((G.lengthMeasure (G.nbhd α I)ᶜ).toReal + I.card * α)) ∧
        G.upperValue α ≤ α / ((G.lengthMeasure (G.nbhd α I)ᶜ).toReal + I.card * α) ∧
        (G.lengthMeasure (G.nbhd α I)ᶜ = 0 → 0 < I.card ∧ G.upperValue α ≤ 1 / I.card)) ∧
    ((∀ v, G.deg v = 1 → α / 2 ≤ G.leafArcLength v) →
      G.IsIndependent α G.leafPoints ∧
        (G.lengthMeasure (G.nbhd α G.leafPoints)ᶜ).toReal = G.totalLength - G.leafCount * α / 2 ∧
        G.upperValue α ≤ α / (G.totalLength + G.leafCount * α / 2)) := by sorry

end ContPatrol
