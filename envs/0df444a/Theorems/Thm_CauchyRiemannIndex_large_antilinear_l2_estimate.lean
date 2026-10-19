-- Prove2me | Theorems.Thm_CauchyRiemannIndex_large_antilinear_l2_estimate
-- name    : CauchyRiemannIndex.large_antilinear_l2_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T14:09:26.726956+00:00
-- url     : https://prove2.me/theorems/5d23ff3c-aa4c-456c-b1d7-ae8000055098
-- title:
--   L² estimate for Cauchy–Riemann operators with a large antilinear term and only negative zeros
-- statement:
--   Let $n=1$, let $S^\pm$ be continuous loops of symmetric $2\times2$ matrices, and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2\times2}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$. Let $\beta:\mathbb{R}\times S^1\to\mathbb{C}$ be smooth with bounded first derivative, such that $|\beta|$ and $1/|\beta|$ are bounded for large $|s|$, and such that its zeros form a finite set $Z^-$ with the following normal form: for some $r>0$ and every $\zeta\in Z^-$, on the disc $|z|<r$ around $\zeta$ one has $S=0$ and
--   $$\beta(\zeta+z)=\bar z .$$
--   For $\sigma>0$ let $D_\sigma\eta=\partial_s\eta+J_0\partial_t\eta+S\eta+\sigma\beta\bar\eta$, acting from $W^{1,2}$ to $L^2$.
--
--   Then there are $\sigma_0>0$ and $C$ such that for all $\sigma\ge\sigma_0$ and all $\eta\in W^{1,2}$
--   $$\|\eta\|_{L^2}^2\le\frac{C}{\sigma}\,\|D_\sigma\eta\|_{L^2}^2 .$$
--
--   This is the estimate for the case where all zeros of $\beta$ are negative in the setting of Wendl's Proposition 5.27 (§ 5.5); in particular $D_\sigma$ is injective for large $\sigma$.
--
--   **Formalization Note** $\mathbb{C}=\mathbb{R}^2$ via $(x,y)\mapsto x+iy$, and $\eta\mapsto\beta\bar\eta$ is the matrix `antilinearMat β`, so $D_\sigma$ is $D_{S_\sigma}$ with $S_\sigma=S+\sigma\cdot$`antilinearMat ∘ β`, and $\|D_\sigma\eta\|_{L^2}$ is the $L^2$ norm of `crApply` $S_\sigma$ applied to the triple $(\eta,\partial_s\eta,\partial_t\eta)\in$ `W1p 2 1`. Points of the cylinder are pairs $(s,t)$ and $\zeta+z$ means $(\zeta_s+\operatorname{Re}z,\zeta_t+\operatorname{Im}z)$; $\beta$ is $1$-periodic in $t$, and every zero of $\beta$ is a $t$-translate by an integer of a point of $Z^-$. Nondegeneracy of $S^\pm$ is not assumed. The norms are written with `eLpNorm` (values in $[0,\infty]$), and $C/\sigma$ enters through `ENNReal.ofReal`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, § 5.5 (assumptions, p. 94), cf. Lemma 5.22; cylinder, trivial line bundle, p = 2

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- An `L²` estimate for a large antilinear perturbation with only negative zeros, in the setting
of Wendl § 5.5 (p. 94) on the cylinder with the trivial line bundle and `p = 2`: let `D_S` (`n = 1`) be asymptotic to
loops `S±` of symmetric matrices, and let `β : ℝ × S¹ → ℂ` be smooth with bounded derivative, with
`|β|` and `1/|β|` bounded for large `|s|`, whose zeros (mod `t ↦ t + 1`) are the finite set `Z⁻`,
such that on a disc of radius `r` around each zero `ζ` the operator is `∂̄` (`S = 0`) and
`β(ζ + z) = z̄`. Put `D_σ η = D_S η + σ β η̄`. Then there are `σ₀` and `C` with
`‖η‖²_{L²} ≤ (C / σ) ‖D_σ η‖²_{L²}` for all `σ ≥ σ₀` and all `η ∈ W^{1,2}`. -/
theorem large_antilinear_l2_estimate (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zminus : Finset (ℝ × ℝ))
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0) :
    ∃ σ₀ C : ℝ, 0 < σ₀ ∧ ∀ σ ≥ σ₀, ∀ w ∈ W1p 2 1,
      eLpNorm (w.1 : ℝ × ℝ → Vec 1) 2 cylMeasure ^ 2 ≤
        ENNReal.ofReal (C / σ) *
          eLpNorm (crApply (fun x => S x + σ • antilinearMat (β x)) w) 2 cylMeasure ^ 2 := by
  sorry

end CauchyRiemannIndex
