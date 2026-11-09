-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_4_8_derivatives_along_curves
-- name    : DelaunayStretch.lemma_4_8_derivatives_along_curves
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:58:00.305735+00:00
-- url     : https://prove2.me/theorems/87327df8-a418-4b7a-ab09-0a7ab52310a8
-- title:
--   Lemma 4.8 — chain rule along $C^1$ curves with incident gradients
-- statement:
--   Let $H$ be a real function on $\Omega\times\mathbb R$ that is continuous and locally Lipschitz (condition (H0)), with a piecewise $C^1$ structure, and let $z:[t_0,t_1]\to\Omega\times\mathbb R$ be a continuously differentiable curve. Then $H\circ z$ is absolutely continuous, and for almost every $t\in[t_0,t_1]$ there is an incident gradient $\nabla$ of $H$ at $z(t)$ with
--
--   $$
--   (H\circ z)'(t)=\nabla\cdot z'(t).
--   $$
--
--   This is the chain rule used to integrate (H2) and (H4) along the two stages of a step.
--
--   **Formalization Note** The curve is a map $\mathbb R\to\mathbb R^4$ that is $C^1$ on $[t_0,t_1]$ with values in $\Omega\times\mathbb R$ there; absolute continuity is Mathlib's notion on the interval; "almost every" refers to Lebesgue measure on $[t_0,t_1]$.
--
--   Differences from the source:
--   - encoding: z : [t₀, t₁] → Ω × ℝ continuously differentiable → z : ℝ → ℝ⁴ with ContDiffOn ℝ 1 on [t₀, t₁] and values in Ω × ℝ there; reason: only the values on [t₀, t₁] enter; same curves
--   - encoding: H a real function on Ω × ℝ → H : ℝ⁴ → ℝ, z = (γ, φ, θ, ψ); every hypothesis and conclusion reads H only on Ω × ℝ (on Σ for gate states); reason: Ω × ℝ is open in ℝ⁴, so values and derivatives of H there do not depend on the values outside; same functions
--   - encoding: the interval [t₀, t₁] → the hypothesis t₀ ≤ t₁; reason: [t₀, t₁] is an interval, so t₀ ≤ t₁ is implicit in the source; Mathlib's AbsolutelyContinuousOnInterval is stated on uIcc t₀ t₁, so without it t₁ < t₀ would make the hypotheses on the empty Icc t₀ t₁ vacuous while the conclusion constrains H ∘ z on [t₁, t₀]
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Lemma 4.8, p.27

import Mathlib
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Lemma 4.8 (Derivatives along curves)** (p.27). Let `H` be a real function on `Ω × ℝ` that
is continuous and locally Lipschitz, that is, satisfies (H0), with a piecewise `C¹` structure,
and let `z : [t₀, t₁] → Ω × ℝ` be a continuously differentiable curve. Then `H ∘ z` is
absolutely continuous, and for almost every `t ∈ [t₀, t₁]`, there is an incident gradient `∇`
of `H` at `z(t)` with respect to this structure such that `(H ∘ z)′(t) = ∇ · z′(t)`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Lemma 4.8, p.27.

**Formalization Note** The interval `[t₀, t₁]` has `t₀ ≤ t₁` (Mathlib's
`AbsolutelyContinuousOnInterval f t₀ t₁` is stated on `uIcc t₀ t₁`, so without this hypothesis
`t₁ < t₀` would leave the curve unconstrained on the interval of the conclusion). The curve is
`z : ℝ → ℝ⁴`, `C¹` on `[t₀, t₁]` (`ContDiffOn ℝ 1`) with values in `Ω × ℝ` there. Absolute continuity is Mathlib's `AbsolutelyContinuousOnInterval`;
"almost every" is for Lebesgue measure on `[t₀, t₁]`, and `(H ∘ z)′(t) = ∇ · z′(t)` is
`HasDerivAt` with `z′(t) = deriv z t`. -/
theorem lemma_4_8_derivatives_along_curves (H : R4 → ℝ) (hH : CondH0 H) (P : PiecewiseC1 H)
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (z : ℝ → R4) (hz : ContDiffOn ℝ 1 z (Set.Icc t₀ t₁))
    (hzΩ : Set.MapsTo z (Set.Icc t₀ t₁) OmegaTimesR) :
    AbsolutelyContinuousOnInterval (fun t => H (z t)) t₀ t₁ ∧
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc t₀ t₁)),
      ∃ g : R4, P.IncidentGradient (z t) g ∧
        HasDerivAt (fun t => H (z t)) (dot4 g (deriv z t)) t := by sorry

end DelaunayStretch
