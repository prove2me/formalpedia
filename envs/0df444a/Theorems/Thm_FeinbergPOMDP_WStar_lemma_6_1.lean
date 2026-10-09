-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_lemma_6_1
-- name    : FeinbergPOMDP.WStar.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:47.933455+00:00
-- url     : https://prove2.me/theorems/1b6c4b31-09b1-4d05-ad19-d394715469b4
-- title:
--   Lemma 6.1 — a lower semicontinuous cost c gives a lower semicontinuous belief cost c̄ on ℙ(𝕏) × 𝔸
-- statement:
--   Let $\mathbb X$ and $\mathbb A$ be Borel subsets of Polish spaces, and let $\mathbb P(\mathbb X)$ carry the topology of weak convergence. Let $c : \mathbb X \times \mathbb A \to \mathbb R \cup \{+\infty\}$ be bounded below and lower semicontinuous, and let
--   $$\bar c(z, a) = \int_{\mathbb X} c(x, a)\,z(dx), \qquad z \in \mathbb P(\mathbb X),\ a \in \mathbb A,$$
--   be the cost of the belief MDP (3.8). Then $\bar c$ is bounded below and lower semicontinuous on $\mathbb P(\mathbb X) \times \mathbb A$.
--
--   This is the continuity half of Theorem 3.4: it is what makes the level sets of $\bar c$ closed.
--
--   **Formalization Note.** The cost is written $c = \ell + f$ with $\ell \in \mathbb R$ and $f$ Borel with values in $[0, \infty]$, so $\bar c = \ell + \int f(\cdot, a)\,dz$. Adding a real constant preserves lower semicontinuity, so the statement is made for $f$ and $\int f(\cdot, a)\,dz$; boundedness below of $\bar c$ (by $\ell$) holds in this encoding by construction and is not restated.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Lemma 6.1, p. 23

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Lemma 6.1** (p. 23): if `c : 𝕏 × 𝔸 → ℝ̄` is bounded below and lower
semi-continuous on `𝕏 × 𝔸`, then `c̄(z, a) = ∫ c(x, a) z(dx)` (3.8) is bounded below and lower
semi-continuous on `ℙ(𝕏) × 𝔸`.

Formalization Note. `𝕏, 𝕐, 𝔸` are Borel subsets of Polish spaces (p. 4), encoded as separable metrizable spaces with
their Borel σ-algebras (`PolishSpace` is not assumed). The cost is `c = lower + f` with `f : 𝕏 → 𝔸 → [0, ∞]` Borel, so
`c̄ = lower + beliefCost f`. Adding the real constant `lower` preserves lower semicontinuity in both
directions, so the statement is about `f` and `beliefCost f`; "bounded below" holds in this encoding
by construction (`c̄ ≥ lower`) and is not restated. -/
theorem lemma_6_1 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hlsc : LowerSemicontinuous (fun p : X × A => f p.1 p.2)) :
    LowerSemicontinuous (fun p : ProbabilityMeasure X × A => beliefCost f p.1 p.2) := by sorry

end FeinbergPOMDP.WStar
