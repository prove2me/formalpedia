-- Prove2me | Theorems.Thm_ContPatrol_lemma_1
-- name    : ContPatrol.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:48.524991+00:00
-- url     : https://prove2.me/theorems/d0e0ea4c-a0a1-4bc9-9bf5-e4aa91008ad9
-- title:
--   Lemma 1: the uniform attack holds every patrol to $\alpha/\mu$, so $V\le\alpha/\mu$
-- statement:
--   Let $Q$ be a network of total length $\mu$ and let $\alpha>0$.
--
--   1. For every $M\ge0$, against any patrol, the uniform attack strategy with attack interval $[M,M+\alpha]$ is intercepted with probability at most $\alpha/\mu$.
--   2. Consequently
--   $$V\le\frac{\alpha}{\mu}.$$
--
--   This is the general Attacker bound; Theorem 2(ii) shows it is attained whenever $Q$ has a tour covering every point equally often.
--
--   **Formalization Note** "$V\le v$" is stated for the upper value.
--
--   Differences from the source:
--   - encoding: a network Q: a connected graph with positive arc lengths, viewed as a metric space; nodes are the points of degree ≠ 2; the line segment is excluded → MetricGraph V E with IsNetwork: finite types of vertices and edges, src/tgt maps (loops and parallel edges allowed), len e > 0, Nonempty E, connected, and (∃ v, 3 ≤ deg v) ∨ (∀ v, deg v ≠ 1); vertices of degree 2 allowed; points are vertices or interior points of edges; reason: a subdivided arc is the same metric space; every network arises this way, and leaf arcs, girth and reversals are defined subdivision-invariantly
--   - encoding: V, the value of the game (interception probability with best play on both sides) → lowerValue (sup of guarantees of measurable mixed patrols against pure attacks) and upperValue (inf of guarantees of mixed attacks against pure patrols); V ≤ v is upperValue ≤ v, V ≥ v is v ≤ lowerValue, V = v is both equalities; reason: the value, when it exists, is the common value of these two; existence (Garrec 2019) is not assumed
--   - encoding: mixed Patroller strategy → a family S ω of patrols on a probability space (Ω, P) with measurable evaluations ω ↦ S ω t; attacks are probability measures on (point, start time) with no mass on negative start times; reason: interception probabilities are then genuine probabilities; this is the standard meaning of a mixed strategy
--   - generalization: standing assumption 0 < α < µ̄ (p.6) → 0 < α only; reason: the proof (λ(S(J)) ≤ |J| = α, p.29) uses no upper bound on α; the Lean range contains the source's
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Lemma 1, p.7 (proof in the Appendix, p.29)

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_IsNetwork
import Definitions.Def_ContPatrol_MetricGraph_lowerValue
import Definitions.Def_ContPatrol_MetricGraph_uniformAttack

namespace ContPatrol

open MetricGraph

/-- **Lemma 1** (Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Lemma 1, p.7; proof in the Appendix, p.29):
"Against any patrol S, a uniform attack strategy is intercepted with probability not more than
α/µ. Consequently V ≤ α/µ for any network."

For every network and every `α > 0`: for every `M ≥ 0` the uniform attack at time `M` holds every
patrol to interception probability at most `α/µ`, and the upper value is at most `α/µ`.

**Formalization Note.** The paper's standing assumption `α < µ̄` (p.6) is not needed and not
assumed. "V ≤ v" is stated for the upper value. -/
theorem lemma_1 {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MetricGraph V E) (hG : G.IsNetwork) (α : ℝ) (hα : 0 < α) :
    (∀ M : ℝ, 0 ≤ M → G.AttackGuarantee α (G.uniformAttack M) (α / G.totalLength)) ∧
      G.upperValue α ≤ α / G.totalLength := by sorry

end ContPatrol
