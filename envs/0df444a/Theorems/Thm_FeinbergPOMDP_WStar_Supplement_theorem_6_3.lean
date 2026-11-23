-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_Supplement_theorem_6_3
-- name    : FeinbergPOMDP.WStar.Supplement.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:28:29.826978+00:00
-- url     : https://prove2.me/theorems/5d9974d7-a28f-43f9-85ca-286009210548
-- title:
--   Theorem 6.3 — actionwise inf-compact, bounded-below c gives actionwise inf-compact, bounded-below c̄
-- statement:
--   Let $\mathbb X$ and $\mathbb A$ be the state and action spaces, $\mathbb P(\mathbb X)$ the probability measures on $\mathbb X$, and $c:\mathbb X\times\mathbb A\to\overline{\mathbb R}=\mathbb R\cup\{+\infty\}$ a Borel cost. Define $\bar c(z,a)=\int_{\mathbb X}c(x,a)\,z(dx)$ (3.8).
--
--   **Theorem 6.3.** If $a\mapsto c(x,a)$ is inf-compact on $\mathbb A$ for each $x\in\mathbb X$ and $c$ is bounded below on $\mathbb X\times\mathbb A$, then:
--   1. for each $z\in\mathbb P(\mathbb X)$ the function $a\mapsto\bar c(z,a)$ is inf-compact on $\mathbb A$, that is, $\{a\in\mathbb A:\bar c(z,a)\le\lambda\}$ is compact for every $\lambda\in\mathbb R$;
--   2. $\bar c$ is bounded below on $\mathbb P(\mathbb X)\times\mathbb A$.
--
--   No continuity of $c$ in $x$ or joint compactness is assumed; the statement concerns each belief separately.
--
--   **Formalization Note** The bounded-below cost is written $c=\ell+f$ with $\ell\in\mathbb R$ and $f\ge0$ extended-real valued, which carries the hypothesis "bounded below"; then $\bar c=\ell+\int f(\cdot,a)\,dz$, and the bounded-below conclusion is stated as the existence of a real lower bound.
--
--   Differences from the source:
--   - generalization: 𝕏, 𝔸 are Borel subsets of Polish spaces → separable metrizable spaces with their Borel σ-algebras; reason: every Borel subset of a Polish space is separable metrizable, so the source's instances are covered
--   - encoding: a bounded-below Borel cost c : 𝕏 × 𝔸 → ℝ ∪ {+∞}; c̄(z,a) = ∫ c(x,a) z(dx) → c = lower + f with lower : ℝ and Borel f : 𝕏 → 𝔸 → [0,∞] (the hypothesis 'bounded below' is carried by this form); c̄ = lower + ∫⁻ f(·,a) dz, in EReal; reason: every bounded-below ℝ ∪ {+∞}-valued Borel function has this form
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 6.3, p. 24 (proof p. 24)

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_MDPValues

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

namespace FeinbergPOMDP.WStar.Supplement

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 6.3** (p. 24; proof p. 24): if
`c(x, a)` is inf-compact in `a ∈ 𝔸` for each `x ∈ 𝕏` and bounded below on `𝕏 × 𝔸`, then
`c̄(z, a) = ∫ c(x, a) z(dx)` (3.8) is inf-compact in `a ∈ 𝔸` for each `z ∈ ℙ(𝕏)` and bounded below
on `ℙ(𝕏) × 𝔸`.

Formalization Note. `𝕏, 𝔸` are separable metrizable spaces with their Borel σ-algebras (Borel
subsets of Polish spaces are such spaces). The bounded-below Borel cost is written
`c(x, a) = lower + f x a` with `lower : ℝ` and `f : 𝕏 → 𝔸 → [0, ∞]` Borel; every bounded-below
Borel function into `ℝ ∪ {+∞}` has this form, so the hypothesis "bounded below" is carried by the
encoding. `c̄(z, a) = lower + beliefCost f z a`, and the conclusion "bounded below" is stated
explicitly (it holds with the constant `lower`). No joint continuity or `𝕂`-inf-compactness is
assumed. -/
theorem theorem_6_3 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (lower : ℝ) (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hc : ∀ x : X, InfCompact (fun a : A => (lower : EReal) + (f x a : EReal))) :
    (∀ z : ProbabilityMeasure X,
      InfCompact (fun a : A => (lower : EReal) + (beliefCost f z a : EReal))) ∧
    ∃ K : ℝ, ∀ (z : ProbabilityMeasure X) (a : A),
      (K : EReal) ≤ (lower : EReal) + (beliefCost f z a : EReal) := by sorry

end FeinbergPOMDP.WStar.Supplement
