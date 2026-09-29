-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod
-- name    : AutomorphicForm.exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/fd227f95-f0c2-5def-b298-29711bceb630
-- title:
--   Split transfer of twisted orbital integrals for GL₂
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, finite-dimensional with $\operatorname{finrank}_K L = 2$, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $A$ be a commutative $K$-algebra carrying a Hausdorff, locally compact, second-countable topological ring structure. Assume given a group isomorphism $\Psi : GL_2(A)\times GL_2(A) \simeq GL_2(L\otimes_K A)$, continuous with continuous inverse, with $\Psi(g,g) = \mathrm{toTensorGL}\,g$ (the image of $g$ under $a \mapsto 1\otimes a$) for all $g$, and with $\mathrm{sigmaGL}(\Psi p) = \Psi(p_2,p_1)$ for all $p$, where $\mathrm{sigmaGL}$ is induced by $\sigma\otimes\mathrm{id}_A$. Both general linear groups carry their Borel $\sigma$-algebras, $\mu_A$ is a Haar measure on $GL_2(A)$ and $\mu_L$ is the pushforward of $\mu_A\times\mu_A$ along $\Psi$. The conclusion has two parts. First, for every continuous compactly supported $\varphi : GL_2(L\otimes_K A)\to\mathbb{C}$ the fibre integral $f(g)=\int \varphi(\Psi(h,h^{-1}g))\,d\mu_A(h)$ is continuous with compact support. Second, let $\gamma \in GL_2(A)$ be regular semisimple in the sense that $\operatorname{tr}(\gamma)^2-4\det(\gamma)$ is a unit of $A$, let $\delta \in GL_2(L\otimes_K A)$ satisfy `IsNormConjugator K L A σ γ δ 1`, i.e. $\mathrm{toTensorGL}\,\gamma = 1^{-1}\cdot \mathrm{normString}\,\delta\cdot 1$, and let $\tau$, $\tau'$ be Borel measures on the centraliser of $\gamma$ in $GL_2(A)$ and on the $\sigma$-twisted centraliser $\{t : t\delta\,\mathrm{sigmaGL}(t)^{-1}=\delta\}$ which are coupled in the sense that the pushforward of $\tau'$ along $t\mapsto 1^{-1}t\cdot 1$ equals the pushforward of $\tau$ along $\mathrm{toTensorGL}$. Let $C$ be compact, and let $w : GL_2(A)\to\mathbb{R}$ be continuous, compactly supported and non-negative with $\int_{Z(\gamma)} w(tx)\,d\tau(t)=1$ for every $x$ such that $\Psi(h,h^{-1}x^{-1}\gamma x)\in C$ for some $h$. Then there is a continuous, compactly supported, non-negative $w'$ on $GL_2(L\otimes_K A)$ such that for every continuous $\varphi$ with $\operatorname{tsupport}\varphi\subseteq C$: $w$ is a section function for $f$ at $\gamma$ and $w'$ one for $\varphi$ at $\delta$ (non-negativity, measurability, compact support, and the normalisation $\int w(tx)\,d\tau=1$ whenever $f(x^{-1}\gamma x)\neq 0$, respectively $\int w'(tx)\,d\tau'=1$ whenever $\varphi(x^{-1}\delta\,\mathrm{sigmaGL}(x))\neq 0$), and $\int \varphi(x^{-1}\delta\,\mathrm{sigmaGL}(x))\,w'(x)\,d\mu_L = \int f(x^{-1}\gamma x)\,w(x)\,d\mu_A$.
--
--   This is the transfer identity at a split place in Langlands' base change for $GL(2)$: when $L\otimes_K A$ splits, so that $GL_2(L\otimes_K A)$ is the product of two copies of $GL_2(A)$ with $\sigma$ exchanging them, the $\sigma$-twisted orbital integral of $\varphi$ at $\delta$ coincides with the orbital integral at $\gamma$ of the integral of $\varphi$ along the fibres of multiplication, both regularised by section functions against the coupled centraliser measures. It feeds the construction of archimedean test factors used in the comparison of twisted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (Ψ : GL (Fin 2) A × GL (Fin 2) A ≃* GL (Fin 2) (L ⊗[K] A))
    (hΨc : Continuous Ψ) (hΨc' : Continuous Ψ.symm)
    (hΨ₁ : ∀ g : GL (Fin 2) A, Ψ (g, g) = toTensorGL K L A g)
    (hΨσ : ∀ p : GL (Fin 2) A × GL (Fin 2) A, sigmaGL K L A σ (Ψ p) = Ψ p.swap)
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) :
    letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
    μA.IsHaarMeasure → μL = Measure.map Ψ (μA.prod μA) →
    (∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, Continuous φ → HasCompactSupport φ →
      (Continuous fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA) ∧
      (HasCompactSupport fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA)) ∧
    ∀ γ : GL (Fin 2) A, IsRegularSemisimple γ →
    ∀ δ : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ 1 →
    ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
      (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)),
      Coupled K L A σ γ δ 1 τ τ' →
    ∀ C : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact C →
    ∀ w : GL (Fin 2) A → ℝ, Continuous w → HasCompactSupport w → (∀ x, 0 ≤ w x) →
      (∀ x : GL (Fin 2) A, (∃ h : GL (Fin 2) A, Ψ (h, h⁻¹ * (x⁻¹ * γ * x)) ∈ C) →
        ∫ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), w (t * x) ∂τ = 1) →
    ∃ w' : GL (Fin 2) (L ⊗[K] A) → ℝ, Continuous w' ∧ HasCompactSupport w' ∧ (∀ x, 0 ≤ w' x) ∧
      ∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, Continuous φ → tsupport φ ⊆ C →
        IsSectionFnOn A γ τ (fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA) w ∧
        IsTwistedSectionFnOn K L A σ δ τ' φ w' ∧
        ∫ x, φ (x⁻¹ * δ * sigmaGL K L A σ x) * (w' x : ℂ) ∂μL =
          ∫ x, (fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA) (x⁻¹ * γ * x) * (w x : ℂ) ∂μA := by sorry
