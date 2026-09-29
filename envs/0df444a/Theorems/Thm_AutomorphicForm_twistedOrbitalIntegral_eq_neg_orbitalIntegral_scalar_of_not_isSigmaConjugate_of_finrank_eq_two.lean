-- Prove2me | Theorems.Thm_AutomorphicForm_twistedOrbitalIntegral_eq_neg_orbitalIntegral_scalar_of_not_isSigmaConjugate_of_finrank_eq_two
-- name    : AutomorphicForm.twistedOrbitalIntegral_eq_neg_orbitalIntegral_scalar_of_not_isSigmaConjugate_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9c79c812-e58d-50ae-a97f-014ac7761a49
-- title:
--   Twisted orbital integral is minus the scalar orbital integral
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ of degree $\operatorname{finrank}_K L = 2$, let $\sigma : L \simeq_K L$ be an automorphism such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$, and let $v$ be a height-one prime of $\mathcal{O}_K$, with completion $K_v$. Let $\gamma \in GL_2(K_v)$ be a scalar matrix $c\cdot 1$ for some $c \in K_v^\times$, and let $\delta, y \in GL_2(L\otimes_K K_v)$ satisfy the relation that the image of $\gamma$ in $GL_2(L\otimes_K K_v)$ equals $y^{-1}\,(\text{norm string of }\delta\text{ for }\sigma)\,y$. Let $\tau$ be a Haar measure, for the Borel $\sigma$-algebra, on the centraliser of $\{\gamma\}$ in $GL_2(K_v)$, and $\tau'$ a Haar measure, again for the Borel $\sigma$-algebra, on the $\sigma$-twisted centraliser of $\delta$ in $GL_2(L\otimes_K K_v)$. Assume that $\delta$ is not $\sigma$-conjugate to any scalar: for every $z \in (L\otimes_K K_v)^\times$ there is no $x$ with $z\cdot 1 = x^{-1}\,\delta\,\sigma(x)$. Assume the measure normalisation: writing $M$ for the set of elements $t$ of the twisted centraliser whose determinant is the image under $\mathrm{includeRight}$ of some $s \in K_v^\times$ with $|s|_v = 1$, one has $\tau'(M)\cdot N(v) = \tau(\{t \mid t \in \text{the set of units integral together with their inverses}\}) + \tau'(M)$, where $N(v)$ is the absolute norm of $v$. Then for every locally constant, compactly supported $\varphi_v : GL_2(L\otimes_K K_v) \to \mathbb{C}$ and every locally constant, compactly supported $f_v : GL_2(K_v) \to \mathbb{C}$ which match locally for $\sigma$ with respect to the semilocal and local Haar measures, and for all $I, I' \in \mathbb{C}$ such that $I'$ is a twisted orbital integral of $\varphi_v$ at $\delta$ for $\tau'$ and $I$ is an orbital integral of $f_v$ at $\gamma$ for $\tau$, one has $I' = -I$.
--
--   This is the value form, at a non-split finite place of a quadratic extension, of the local comparison underlying quadratic base change for $GL(2)$: for a central element $\gamma$ whose twisted class is not that of a scalar, the twisted centraliser is the unit group of a quaternion division algebra, and under the Jacquet–Langlands normalisation relating the measure of its maximal compact to $\tau(GL_2(\mathcal{O}_v))$ by the factor $N(v)-1$, the proportionality constant between twisted and ordinary orbital integrals is exactly $-1$. It is used in the construction of Haar measures for which the twisted orbital integral at a norm of a scalar is computed as a multiple of the corresponding local integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_twistedOrbitalIntegral_eq_neg_orbitalIntegral_scalar_of_not_isSigmaConjugate_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.twistedOrbitalIntegral_eq_neg_orbitalIntegral_scalar_of_not_isSigmaConjugate_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : ∃ c : (v.adicCompletion K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ y)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (hnorm : letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
      letI := AutomorphicForm.localCentralizerBorel K v γ
      τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} +
          τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}) :
    ∀ (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ), AutomorphicForm.IsSemiLocalTestFn K L v φv →
    ∀ (fv : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v fv →
      AutomorphicForm.AreMatchingLocal K L v σ φv fv →
      ∀ I I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I' →
        AutomorphicForm.IsOrbitalIntegral K v γ τ fv I → I' = (-1 : ℂ) * I := by sorry
