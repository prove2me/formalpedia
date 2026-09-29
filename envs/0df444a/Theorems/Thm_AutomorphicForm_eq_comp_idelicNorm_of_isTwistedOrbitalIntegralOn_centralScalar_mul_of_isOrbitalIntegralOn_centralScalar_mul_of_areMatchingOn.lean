-- Prove2me | Theorems.Thm_AutomorphicForm_eq_comp_idelicNorm_of_isTwistedOrbitalIntegralOn_centralScalar_mul_of_isOrbitalIntegralOn_centralScalar_mul_of_areMatchingOn
-- name    : AutomorphicForm.eq_comp_idelicNorm_of_isTwistedOrbitalIntegralOn_centralScalar_mul_of_isOrbitalIntegralOn_centralScalar_mul_of_areMatchingOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/41e2c0b6-febe-56fc-b114-df06d1026a5e
-- title:
--   Matching transports central translates along the idelic norm
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite Galois, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of the Galois group lies in the subgroup of integer powers of $\sigma$. Let $\mu$ be a measure on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ for the Borel structure, $c_0' \in \mathbb{R}_{\ge 0}$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ and $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy `AreMatchingOn`: for every $\delta$ whose norm string $\delta \cdot \sigma(\delta) \cdots \sigma^{[L:K]-1}(\delta)$ is regular semisimple (its $\mathrm{tr}^2 - 4\det$ is a unit), every regular semisimple $\gamma$ conjugated to that norm string by some $y$, and every coupled pair of Haar measures on the centraliser of $\gamma$ and the $\sigma$-twisted centraliser of $\delta$, each twisted orbital integral value of $\varphi \circ \mathrm{baseChange}$ at $\delta$ against $\mu$ equals each orbital integral value of $f$ at $\gamma$ against $c_0' \cdot$ (adelic Haar measure), and orbital integrals of $f$ at regular semisimple classes that are not norms vanish. Fix such $\delta$, $\gamma$, $y$, and coupled Haar measures $\tau_K$, $\tau'$, the coupling being equality of the pushforward of $\tau'$ under $t \mapsto y^{-1} t y$ with the pushforward of $\tau_K$ along the inclusion $\mathrm{GL}_2(\mathbb{A}_K) \to \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$. Suppose $I_L(w)$ is, for each idele $w \in \mathbb{A}_L^\times$, a twisted orbital integral value at $\delta$ of the central translate $g \mapsto \varphi(w \cdot g)$ base-changed, and $I_K(z)$ is, for each $z \in \mathbb{A}_K^\times$, an orbital integral value at $\gamma$ of $g \mapsto f(z \cdot g)$, central translates being by scalar matrices. Then $I_L(w) = I_K(N(w))$ for all $w$, where $N$ is the idelic norm $\mathbb{A}_L^\times \to \mathbb{A}_K^\times$ induced by the algebra norm attached to the adelic base-change homomorphism.
--
--   This is the per-class, per-central-translate form of the adelic matching of test functions in cyclic base change for $\mathrm{GL}_2$: translating $\varphi$ by a central idele $w$ shifts the relevant norm class by the scalar matrix at $N_{L/K}(w)$, so the twisted orbital integrals of the translated function are computed by the orbital integrals of $f$ translated by the norm. It feeds the comparison of hyperbolic contributions and fixes the normalisation of the $K$-side class integrals used there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_comp_idelicNorm_of_isTwistedOrbitalIntegralOn_centralScalar_mul_of_isOrbitalIntegralOn_centralScalar_mul_of_areMatchingOn.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.eq_comp_idelicNorm_of_isTwistedOrbitalIntegralOn_centralScalar_mul_of_isOrbitalIntegralOn_centralScalar_mul_of_areMatchingOn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (c₀' : NNReal)
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hMatch : AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ μ
      (c₀' • adelicGLHaar (Fin 2) (𝓞 K) K) (φ ∘ AutomorphicForm.baseChangeGL K L) f)

    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (hy : AutomorphicForm.IsNormConjugator K L (AdeleRing (𝓞 K) K) σ γ δ y)
    (τK : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    [τK.IsHaarMeasure]
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)) [τ'.IsHaarMeasure]
    (hc : AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ γ δ y τK τ')

    (IL : (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (hIL : ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ'
        ((fun g : GL (Fin 2) (AdeleRing (𝓞 L) L) => φ (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
          AutomorphicForm.baseChangeGL K L) (IL w))
    (IK : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIK : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀' • adelicGLHaar (Fin 2) (𝓞 K) K) γ τK
        (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (IK z)) :
    ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      IL w = IK ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w) := by sorry
