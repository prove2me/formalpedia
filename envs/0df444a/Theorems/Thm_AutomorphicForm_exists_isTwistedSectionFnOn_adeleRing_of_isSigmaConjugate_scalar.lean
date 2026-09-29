-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isSigmaConjugate_scalar
-- name    : AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isSigmaConjugate_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/06baf019-e3df-5b33-a76a-d7c02266fe6d
-- title:
--   Twisted section functions exist at scalar twisted classes
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a finite Galois extension, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $K$-automorphism of $L$ lies in the subgroup of integral powers of $\sigma$. Write $G' = \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $K$, and let $\sigma$ act on $G'$ entrywise through the automorphism of $L \otimes_K \mathbb{A}_K$ induced by $\sigma$ on the left factor; denote this group automorphism by `sigmaGL`. Let $\delta \in G'$ and assume that $\delta$ is $\sigma$-conjugate to a scalar matrix, i.e. there are a unit $d$ of $L \otimes_K \mathbb{A}_K$ and $x \in G'$ with $x^{-1}\,\delta\,\sigma(x) = d \cdot 1$. Let $T' = \{t \in G' : t\,\delta\,\sigma(t)^{-1} = \delta\}$ be the $\sigma$-twisted centraliser of $\delta$, equipped with the Borel $\sigma$-algebra of its subspace topology, and let $\tau'$ be a Haar measure on $T'$. Finally let $\varphi : G' \to \mathbb{C}$ have compact support. Then there exists $w : G' \to \mathbb{R}$ which is everywhere nonnegative, Borel measurable for the Borel structure on $G'$, of compact support, and such that $\int_{T'} w(t x)\, d\tau'(t) = 1$ for every $x \in G'$ with $\varphi(x^{-1}\,\delta\,\sigma(x)) \neq 0$; that is, $w$ is a twisted section function for $\varphi$ at $\delta$ relative to $\tau'$.
--
--   This is the convergence statement for adelic twisted orbital integrals at the twisted classes whose norm is central, packaged as the existence of a section function $w$ cutting the $T'$-orbits of the support of $x \mapsto \varphi(x^{-1}\delta\,\sigma(x))$, so that $\int_{T' \backslash G'} \varphi(x^{-1}\delta\,\sigma(x))\,dx$ may be computed as $\int_{G'} \varphi(x^{-1}\delta\,\sigma(x))\,w(x)\,dx$. It is used in the base-change comparison of integrals over twisted centraliser domains with the corresponding values at central scalars, where a transfer hypothesis is phrased through such section functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isSigmaConjugate_scalar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isSigmaConjugate_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : ∃ d : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsSigmaConjugate K L (AdeleRing (𝓞 K) K) σ δ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) d))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ' φ w := by sorry
