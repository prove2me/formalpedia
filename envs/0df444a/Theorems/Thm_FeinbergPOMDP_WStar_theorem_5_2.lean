-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_theorem_5_2
-- name    : FeinbergPOMDP.WStar.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:53.714853+00:00
-- url     : https://prove2.me/theorems/bc0e441b-5316-4855-8510-5fffa3b5e6bf
-- title:
--   Theorem 5.2 — integrating an equicontinuous family over an open set against a weakly continuous kernel keeps it equicontinuous
-- statement:
--   Let $\mathbb S_1, \mathbb S_2, \mathbb S_3$ be metric spaces with $\mathbb S_2$ separable, and let $\Psi(ds_2 \mid s_1)$ be a weakly continuous stochastic kernel on $\mathbb S_2$ given $\mathbb S_1$. A family $\mathcal A_0$ of real functions on a metric space $\mathbb S$ is **equicontinuous at** $s$ if $\sup_{f \in \mathcal A_0} |f(s') - f(s)| \to 0$ as $s' \to s$, and **uniformly bounded** if there is $M < \infty$ with $|f(s)| \le M$ for all $s$ and all $f \in \mathcal A_0$.
--
--   Let $\mathcal A_0$ be a family of bounded continuous functions on $\mathbb S_2 \times \mathbb S_3$ that is equicontinuous at every point and uniformly bounded. Then for every open set $\mathcal O \subseteq \mathbb S_2$ the family
--   $$\mathcal A_{\mathcal O} = \Big\{(s_1, s_3) \mapsto \int_{\mathcal O} f(s_2, s_3)\,\Psi(ds_2 \mid s_1) : f \in \mathcal A_0\Big\}$$
--   on $\mathbb S_1 \times \mathbb S_3$ is equicontinuous at every point and uniformly bounded.
--
--   Applied twice, this result yields the equicontinuity of the families $\mathcal R_{\mathcal O}$ in Lemma 5.3.
--
--   **Formalization Note.** The metric spaces are metrizable topological spaces ($\mathbb S_2$ with its Borel σ-algebra, separability as `SeparableSpace`). $\mathcal A_0$ is an indexed family $F : \iota \to \mathbb S_2 \times \mathbb S_3 \to \mathbb R$; the equicontinuity above is Mathlib's `EquicontinuousAt`. $\Psi$ is the map $s_1 \mapsto \Psi(\cdot \mid s_1)$, weakly continuous in the sequential sense.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 5.2, p. 17 (definitions of equicontinuity and uniform boundedness, p. 17)

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 5.2** (p. 17): let `𝕊₁, 𝕊₂, 𝕊₃` be metric spaces, `Ψ(ds₂ | s₁)` a
weakly continuous stochastic kernel on `𝕊₂` given `𝕊₁`, and `𝒜₀ ⊆ ℂ(𝕊₂ × 𝕊₃)` equicontinuous at all
points and uniformly bounded. If `𝕊₂` is separable, then for every open `𝒪 ⊆ 𝕊₂` the family
`𝒜_𝒪 = {(s₁, s₃) ↦ ∫_𝒪 f(s₂, s₃) Ψ(ds₂ | s₁) : f ∈ 𝒜₀}` is equicontinuous at all points of
`𝕊₁ × 𝕊₃` and uniformly bounded.

Formalization Note. Metric spaces are metrizable topological spaces (`𝕊₂` with its Borel
σ-algebra). `𝒜₀` is an indexed family `F : ι → 𝕊₂ × 𝕊₃ → ℝ`. The paper's "equicontinuous at `s`"
(p. 17: `sup_{f ∈ 𝒜₀} |f(s′) − f(s)| → 0` as `s′ → s`) is Mathlib's `EquicontinuousAt`; "uniformly
bounded" is one constant `M` for all members and all points. `Ψ` is the map `s₁ ↦ Ψ(· | s₁)` into
`ℙ(𝕊₂)`. -/
theorem theorem_5_2 {S₁ S₂ S₃ ι : Type*}
    [TopologicalSpace S₁] [TopologicalSpace.MetrizableSpace S₁]
    [TopologicalSpace S₂] [TopologicalSpace.MetrizableSpace S₂] [TopologicalSpace.SeparableSpace S₂]
    [MeasurableSpace S₂] [BorelSpace S₂]
    [TopologicalSpace S₃] [TopologicalSpace.MetrizableSpace S₃]
    (Ψ : S₁ → ProbabilityMeasure S₂) (hΨ : IsWeaklyContinuous Ψ)
    (F : ι → S₂ × S₃ → ℝ) (hFc : ∀ i, Continuous (F i))
    (hFeq : ∀ p : S₂ × S₃, EquicontinuousAt F p)
    (hFb : ∃ M : ℝ, ∀ i p, |F i p| ≤ M)
    (O : Set S₂) (hO : IsOpen O) :
    (∀ p : S₁ × S₃, EquicontinuousAt
        (fun i (q : S₁ × S₃) => ∫ s₂ in O, F i (s₂, q.2) ∂(Ψ q.1 : Measure S₂)) p) ∧
    ∃ M : ℝ, ∀ i (q : S₁ × S₃), |∫ s₂ in O, F i (s₂, q.2) ∂(Ψ q.1 : Measure S₂)| ≤ M := by sorry

end FeinbergPOMDP.WStar
