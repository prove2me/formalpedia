-- Prove2me | Theorems.Thm_ApproxDegComp_lemma_21
-- name    : ApproxDegComp.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:32:58.537745+00:00
-- url     : https://prove2.me/theorems/e17a5fb9-d98d-423a-8362-8ae3fcd3b8d6
-- title:
--   Lemma 21 — the probability family $\rho_\theta(x)=|(e^{i\theta A}v)_x|^2$ with $\nu_{(1+z)/2}=\rho_0+\frac z\kappa\rho_0'$
-- statement:
--   Let $\mathcal X\subseteq\{0,1\}^m$ be nonempty, $g:\{0,1\}^m\to\{0,1\}$, $A$ a real symmetric matrix on $\mathbb R^{\mathcal X}$, $P_b=M_{\mathbf 1\{g=b\}}$, and suppose $\lambda=\|P_0AP_1\|>0$; put $\kappa=2\lambda$. Then there are real unit vectors $u_0\in P_0\mathbb R^{\mathcal X}$ and $u_1\in P_1\mathbb R^{\mathcal X}$ with
--
--   $$P_0Au_1=\lambda u_0,\qquad P_1Au_0=\lambda u_1,$$
--
--   such that, for $v=(u_0+iu_1)/\sqrt2$ and $\rho_\theta(x)=|(e^{i\theta A}v)_x|^2$:
--
--   1. every $\rho_\theta$, $\theta\in\mathbb R$, is a probability measure;
--   2. there are probability measures $\nu_0,\nu_1$ supported on $\mathcal X\cap g^{-1}(0)$ and $\mathcal X\cap g^{-1}(1)$ respectively with
--   $$\rho_0=\frac{\nu_0+\nu_1}2,\qquad\rho_0'=\frac\kappa2(\nu_1-\nu_0);$$
--   3. consequently, for $z\in\{-1,1\}$, $\nu_{(1+z)/2}=\rho_0+\frac z\kappa\rho_0'$.
--
--   Here $\rho_0'$ is the derivative of $\theta\mapsto\rho_\theta$ at $0$. The family moves, to first order, from the uniform mixture of $\nu_0,\nu_1$ towards one of them, which is what lets the squarefree extraction of Lemma 9 recover a product of the $\nu$'s.
--
--   **Formalization Note** $\rho_\theta$ is extended by $0$ outside $\mathcal X$; $\nu_b$ for $b\in\{0,1\}$ is indexed by a Boolean.
--
--   Differences from the source:
--   - generalization: X, A, λ, P₀, P₁ "as defined in previous Lemma 20" → any nonempty X ⊆ {0,1}^m, any real symmetric A on ℝ^X and any g with λ = ‖P₀AP₁‖ > 0; reason: Lemma 20's X and A are of this kind, with λ ≥ d/3 > 0 because a non-constant g has d ≥ 1, so the statement specializes to the source's
--   - encoding: ρ_θ : X → [0,1] → ρ_θ on {0,1}^m, equal to 0 outside X; reason: the values on X are unchanged; Lemma 9 needs measures on {0,1}^m
--   - encoding: ν supported on X ∩ g⁻¹(b) → ν b x ≠ 0 implies x ∈ X and g x = b; reason: the definition of support of a finite measure
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 21, p.22 (proof Appendix B, pp.47–48)

import Mathlib
import Definitions.Def_ApproxDegComp_mulOp
import Definitions.Def_ApproxDegComp_rho
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_ApproxDegComp_zOf
import Definitions.Def_LiqPremiaEq_opNorm

namespace ApproxDegComp

/-- **Lemma 21**, p.22 (proof in Appendix B, pp.47–48).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 21, p.22: "Let X, A, λ, P₀, P₁ be as defined in previous Lemma 20 and κ = 2λ. There
exist real unit vectors u₀ ∈ P₀ℝ^X and u₁ ∈ P₁ℝ^X such that P₀Au₁ = λu₀, P₁Au₀ = λu₁. Define
v = (u₀ + iu₁)/√2 and for real θ, define ρ_θ : X → [0, 1] by ρ_θ(x) = |(e^{iθA}v)_x|². Then
{ρ_θ : θ ∈ ℝ} is a family of probability measures. Also, there are probability measures ν₀ and
ν₁ supported on X ∩ g⁻¹(0) and X ∩ g⁻¹(1) respectively, such that ρ₀ = (ν₀ + ν₁)/2,
ρ′₀ = (κ/2)(ν₁ − ν₀). Consequently, for z ∈ {−1, 1} ν_{(1+z)/2} = ρ₀ + (z/κ)ρ′₀."

**Formalization Note** Stated for every nonempty `X`, real symmetric `A` on `ℝ^X` and
`λ = ‖P₀AP₁‖ > 0` (Lemma 20's `X, A` are such, with `λ ≥ d/3 > 0`). `ρ_θ` is `rho X A v θ`,
extended by `0` outside `X`; `ν_b` is `ν b` and `z = zOf b`. `u ∈ P_b ℝ^X` is `P_b u = u`;
`ρ′₀(x)` is the derivative of `θ ↦ ρ_θ(x)` at `0`. -/
theorem lemma_21 (m : ℕ) (g : (Fin m → Bool) → Bool) (X : Finset (Fin m → Bool))
    (hX : X.Nonempty) (A : Matrix X X ℝ) (hA : A.transpose = A) (lam : ℝ)
    (hlam : lam = LiqPremiaEq.opNorm (pmat g X false * A * pmat g X true)) (hlam_pos : 0 < lam)
    (κ : ℝ) (hκ : κ = 2 * lam) :
    ∃ u₀ u₁ : X → ℝ, ∑ x, u₀ x ^ 2 = 1 ∧ ∑ x, u₁ x ^ 2 = 1 ∧
      (pmat g X false).mulVec u₀ = u₀ ∧ (pmat g X true).mulVec u₁ = u₁ ∧
      (pmat g X false * A).mulVec u₁ = lam • u₀ ∧ (pmat g X true * A).mulVec u₀ = lam • u₁ ∧
      ∀ v : X → ℂ, (∀ x, v x = ((u₀ x : ℂ) + Complex.I * (u₁ x : ℂ)) / (Real.sqrt 2 : ℂ)) →
        (∀ θ : ℝ, MemoryRegret.IsProbVec (rho X A v θ)) ∧
        ∃ ν : Bool → (Fin m → Bool) → ℝ,
          (∀ b, MemoryRegret.IsProbVec (ν b) ∧ ∀ x, ν b x ≠ 0 → x ∈ X ∧ g x = b) ∧
          (∀ x, rho X A v 0 x = (ν false x + ν true x) / 2) ∧
          (∀ x, deriv (fun θ => rho X A v θ x) 0 = κ / 2 * (ν true x - ν false x)) ∧
          (∀ b x, ν b x = rho X A v 0 x + zOf b / κ * deriv (fun θ => rho X A v θ x) 0) := by sorry

end ApproxDegComp
