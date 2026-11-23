-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_Supplement_theorem_6_2
-- name    : FeinbergPOMDP.WStar.Supplement.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:26:24.040888+00:00
-- url     : https://prove2.me/theorems/e516d340-a3e0-4037-bad4-bc7bd66ba18e
-- title:
--   Theorem 6.2 — an inf-compact cost c on 𝕏 × 𝔸 gives an inf-compact belief cost c̄ on ℙ(𝕏) × 𝔸
-- statement:
--   Let $\mathbb X$ and $\mathbb A$ be the state and action spaces, $\mathbb P(\mathbb X)$ the probability measures on $\mathbb X$ with the topology of weak convergence, and $c:\mathbb X\times\mathbb A\to\overline{\mathbb R}=\mathbb R\cup\{+\infty\}$ a Borel cost. Define $\bar c(z,a)=\int_{\mathbb X}c(x,a)\,z(dx)$ (3.8). A function is inf-compact if all its level sets $\{\le\lambda\}$, $\lambda\in\mathbb R$, are compact.
--
--   **Theorem 6.2.** If $c$ is inf-compact on $\mathbb X\times\mathbb A$, then $\bar c$ is inf-compact on $\mathbb P(\mathbb X)\times\mathbb A$: for every $\lambda\in\mathbb R$,
--   $$\{(z,a)\in\mathbb P(\mathbb X)\times\mathbb A:\ \bar c(z,a)\le\lambda\}\ \text{is compact.}$$
--
--   Together with Theorem 3.1(vi), it yields inf-compactness of the optimal values of the COMDP.
--
--   **Formalization Note** An inf-compact function is bounded below, so the cost is written $c=\ell+f$ with $\ell\in\mathbb R$ and $f\ge0$ extended-real valued, and $\bar c=\ell+\int f(\cdot,a)\,dz$.
--
--   Differences from the source:
--   - generalization: 𝕏, 𝔸 are Borel subsets of Polish spaces → separable metrizable spaces with their Borel σ-algebras; reason: every Borel subset of a Polish space is separable metrizable, so the source's instances are covered
--   - encoding: an inf-compact Borel cost c : 𝕏 × 𝔸 → ℝ ∪ {+∞}; c̄(z,a) = ∫ c(x,a) z(dx) → c = lower + f with lower : ℝ and Borel f : 𝕏 → 𝔸 → [0,∞]; c̄ = lower + ∫⁻ f(·,a) dz, in EReal; reason: an inf-compact function is bounded below (p. 23), so it has this form; the integral is exact also when c = +∞ on a z-positive set
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 6.2, p. 23 (proof pp. 23–24)

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_MDPValues

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

namespace FeinbergPOMDP.WStar.Supplement

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 6.2** (p. 23; proof pp. 23–24): if
`c : 𝕏 × 𝔸 → ℝ ∪ {+∞}` is inf-compact on `𝕏 × 𝔸`, then `c̄(z, a) = ∫ c(x, a) z(dx)` (3.8) is
inf-compact on `ℙ(𝕏) × 𝔸` (with the topology of weak convergence on `ℙ(𝕏)`).

Formalization Note. `𝕏, 𝔸` are separable metrizable spaces with their Borel σ-algebras (Borel
subsets of Polish spaces are such spaces). The Borel cost is written `c(x, a) = lower + f x a` with
`lower : ℝ`, `f : 𝕏 → 𝔸 → [0, ∞]`; an inf-compact function is bounded below (p. 23), so every
inf-compact Borel cost has this form, and `c̄(z, a) = lower + beliefCost f z a`. Inf-compactness
(`InfCompact`) means that every level set `{c ≤ λ}`, `λ ∈ ℝ`, is compact. -/
theorem theorem_6_2 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (lower : ℝ) (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hc : InfCompact (fun p : X × A => (lower : EReal) + (f p.1 p.2 : EReal))) :
    InfCompact (fun p : ProbabilityMeasure X × A =>
      (lower : EReal) + (beliefCost f p.1 p.2 : EReal)) := by sorry

end FeinbergPOMDP.WStar.Supplement
