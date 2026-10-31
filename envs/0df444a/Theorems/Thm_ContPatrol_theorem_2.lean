-- Prove2me | Theorems.Thm_ContPatrol_theorem_2
-- name    : ContPatrol.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:39.321169+00:00
-- url     : https://prove2.me/theorems/e7f492d0-66ea-43cc-8b2d-0a641d3b72a6
-- title:
--   Theorem 2: a $k$-covering tour guarantees $k\alpha/L$; if $L=k\mu$ the value is $\alpha/\mu$
-- statement:
--   Let $Q$ be a network of total length $\mu$ and $\alpha>0$. Let $S:[0,L]\to Q$ be a closed unit speed path that visits every point of $Q$ at $k\ge1$ times which are separated by at least $\alpha$ (mod $L$), and let $\tilde S$ be its randomized periodic extension.
--
--   1. $\tilde S$ intercepts any attack with probability at least
--   $$\frac{k\alpha}{L}.$$
--   2. If $L=k\mu$, then $\tilde S$ guarantees $\alpha/\mu$, every uniform attack strategy (any $M\ge0$) holds every patrol to $\alpha/\mu$, and
--   $$V=\frac{\alpha}{\mu}.$$
--
--   This is the paper's general Patroller bound; Lemma 4 applies it with $k=2$ to the leaf-pausing tour.
--
--   **Formalization Note** The separation is read cyclically (including the gap across the end of the period). "Optimal" is stated as: each strategy guarantees $\alpha/\mu$ and lower value $=$ upper value $=\alpha/\mu$.
--
--   Differences from the source:
--   - encoding: a network Q: a connected graph with positive arc lengths, viewed as a metric space; nodes are the points of degree ≠ 2; the line segment is excluded → MetricGraph V E with IsNetwork: finite types of vertices and edges, src/tgt maps (loops and parallel edges allowed), len e > 0, Nonempty E, connected, and (∃ v, 3 ≤ deg v) ∨ (∀ v, deg v ≠ 1); vertices of degree 2 allowed; points are vertices or interior points of edges; reason: a subdivided arc is the same metric space; every network arises this way, and leaf arcs, girth and reversals are defined subdivision-invariantly
--   - encoding: V, the value of the game (interception probability with best play on both sides) → lowerValue (sup of guarantees of measurable mixed patrols against pure attacks) and upperValue (inf of guarantees of mixed attacks against pure patrols); V ≤ v is upperValue ≤ v, V ≥ v is v ≤ lowerValue, V = v is both equalities; reason: the value, when it exists, is the common value of these two; existence (Garrec 2019) is not assumed
--   - encoding: mixed Patroller strategy → a family S ω of patrols on a probability space (Ω, P) with measurable evaluations ω ↦ S ω t; attacks are probability measures on (point, start time) with no mass on negative start times; reason: interception probabilities are then genuine probabilities; this is the standard meaning of a mixed strategy
--   - generalization: standing assumption 0 < α < µ̄ (p.6) → 0 < α only; reason: the proof (the shifts Δ that intercept form a set of length kα) uses no upper bound on α; the Lean range contains the source's
--   - reading: visits every point of Q at k times which are separated by at least α (mod L) → VisitsSeparated: α ≤ L and k visit times in [0, L) with all cyclic gaps ≥ α; reason: the non-cyclic reading makes (i) false: a circle of length L = 1 with α = 2, k = 1 would give kα/L = 2 > 1
--   - encoding: S : [0, L] → Q is a closed unit speed tour → IsClosedUnitSpeedPath S L (S : ℝ → Q, 0 < L, S 0 = S L, 1-Lipschitz on [0, L]) and 0 < k; reason: a path visiting every point k ≥ 1 times is a tour; values of S outside [0, L] are never used
--   - encoding: S̃ and the uniform attack strategy are optimal and the value is α/µ → S̃ guarantees α/µ, every uniform attack with M ≥ 0 holds every patrol to α/µ, lowerValue = upperValue = α/µ; reason: optimality of a strategy means it guarantees the value
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Theorem 2, p.9

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_IsNetwork
import Definitions.Def_ContPatrol_MetricGraph_lowerValue
import Definitions.Def_ContPatrol_MetricGraph_uniformAttack
import Definitions.Def_ContPatrol_MetricGraph_periodicExt

namespace ContPatrol

open MetricGraph

/-- **Theorem 2** (Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Theorem 2, p.9):
"Suppose S : [0, L] → Q is a closed unit speed tour that visits every point of Q at k times which
are separated by at least α (mod L). Suppose S̃ is the randomized periodic extension of S (from
Definition 4). Then we have (i) S̃ intercepts any attack with probability at least kα/L.
(ii) If L = kµ, then the randomized periodic extension S̃ (for the Patroller) and a uniform attack
strategy (for the Attacker) are optimal and the value of the game is given by α/µ."

**Formalization Note.** The randomized periodic extension is the family `Δ ↦ periodicExt S L Δ`
under `shiftLaw L` (`Δ` uniform on `[0, L]`). The separation is read cyclically
(`VisitsSeparated`). `0 < k` encodes that `S` is a tour (it visits every point). In (ii),
optimality is stated as: `S̃` guarantees `α/µ`, every uniform attack (any `M ≥ 0`) holds every
patrol to `α/µ`, and lower value = upper value = `α/µ`. The standing assumption `α < µ̄` is not
assumed. -/
theorem theorem_2 {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : MetricGraph V E) (hG : G.IsNetwork) (α : ℝ) (hα : 0 < α)
    (S : ℝ → G.Point) (L : ℝ) (k : ℕ) (hk : 0 < k)
    (hS : G.IsClosedUnitSpeedPath S L) (hvis : G.VisitsSeparated S L α k) :
    G.PatrolGuarantee α (shiftLaw L) (periodicExt S L) (k * α / L) ∧
      (L = k * G.totalLength →
        G.PatrolGuarantee α (shiftLaw L) (periodicExt S L) (α / G.totalLength) ∧
        (∀ M : ℝ, 0 ≤ M → G.AttackGuarantee α (G.uniformAttack M) (α / G.totalLength)) ∧
        G.lowerValue α = α / G.totalLength ∧ G.upperValue α = α / G.totalLength) := by sorry

end ContPatrol
