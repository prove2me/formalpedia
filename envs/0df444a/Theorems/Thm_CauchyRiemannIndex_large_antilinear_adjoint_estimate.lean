-- Prove2me | Theorems.Thm_CauchyRiemannIndex_large_antilinear_adjoint_estimate
-- name    : CauchyRiemannIndex.large_antilinear_adjoint_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T14:02:43.617284+00:00
-- url     : https://prove2.me/theorems/94a5b7cb-469e-44c8-ae07-f660a0b8e92a
-- title:
--   Estimate for the adjoint of a Cauchy–Riemann operator with a large antilinear term and positive zeros
-- statement:
--   Let $S^\pm$ be continuous loops of symmetric $2\times2$ matrices and let $S:\mathbb R\times S^1\to\mathbb R^{2\times2}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$. Let $\beta:\mathbb R\times S^1\to\mathbb C$ be smooth with bounded first derivative, such that $|\beta|$ and $1/|\beta|$ are bounded for large $|s|$, and whose zeros form a finite set $Z^+$ with the following normal form: for some $r>0$ and every $\zeta\in Z^+$, on the disc $|z|<r$ around $\zeta$ one has $S=0$ and $\beta(\zeta+z)=z$. For $\sigma\in\mathbb R$ let $D_\sigma\eta=\partial_s\eta+J_0\partial_t\eta+S\eta+\sigma\beta\bar\eta$ and let
--   $$D_\sigma^*\varphi=-\partial_s\varphi+J_0\partial_t\varphi+\big(S+\sigma A(\beta)\big)^{T}\varphi$$
--   be its formal adjoint, where $A(\beta)$ is the matrix of $z\mapsto\beta\bar z$. Then there is $\sigma_0$ such that for all $\sigma\ge\sigma_0$ and every test section $\varphi$,
--   $$\|\varphi\|_{L^2}\le\|D_\sigma^*\varphi\|_{L^2}.$$
--
--   This is the injectivity estimate for the adjoint of $D_\sigma$ in Wendl's § 5.5 when all zeros of $\beta$ are positive; it gives the surjectivity of $D_\sigma$ in Proposition 5.24.
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and integrals over $\mathbb R\times S^1$ are over the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$); $\partial_s,\partial_t$ are `partialS`, `partialT`, and matrices act through `Matrix.toEuclideanLin`. $\mathbb C=\mathbb R^2$ via $(x,y)\mapsto x+iy$, $A(\beta)$ is `antilinearMat β`, and $D_\sigma$ is $D_{S_\sigma}$ with $S_\sigma=S+\sigma\cdot$`antilinearMat ∘ β`. Points of the cylinder are pairs $(s,t)$ and $\zeta+z$ means $(\zeta_s+\operatorname{Re}z,\zeta_t+\operatorname{Im}z)$; $\beta$ is $1$-periodic in $t$, the zeros are listed in $\mathbb R\times[0,1)$, and every zero of $\beta$ is a $t$-translate by an integer of a listed one. The norms are squared and integrated over `cylMeasure`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, § 5.5, pp. 94–100, with the assumptions of Proposition 5.24 (n = 1, p = 2)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, § 5.5 (p. 94), with the assumptions of Proposition 5.24, on the cylinder with the
trivial line bundle: let `D_S` (`n = 1`) be asymptotic to loops `S±` of symmetric matrices, and let
`β : ℝ × S¹ → ℂ` be smooth with bounded derivative, with `|β|` and `1/|β|` bounded for large `|s|`,
whose zeros (mod `t ↦ t + 1`) are the finite set `Z⁺`, such that on a disc of radius `r` around each
zero `ζ` one has `S = 0` and `β(ζ + z) = z`. Then for all large `σ`, every test section `φ`
satisfies `‖φ‖₂ ≤ ‖D_σ^* φ‖₂`, where `D_σ^* φ = -∂ₛφ + J₀ ∂ₜφ + (S + σ A(β))ᵀ φ` is the formal
adjoint of `D_σ = D_S + σ β ·̄`. -/
theorem large_antilinear_adjoint_estimate (Splus Sminus : ℝ → Mat 1)
    (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ φ : ℝ × ℝ → Vec 1, IsTestSection φ →
      ∫ x, ‖φ x‖ ^ 2 ∂cylMeasure ≤
        ∫ x, ‖-partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
          Matrix.toEuclideanLin (S x + σ • antilinearMat (β x))ᵀ (φ x)‖ ^ 2 ∂cylMeasure := by
  sorry

end CauchyRiemannIndex
