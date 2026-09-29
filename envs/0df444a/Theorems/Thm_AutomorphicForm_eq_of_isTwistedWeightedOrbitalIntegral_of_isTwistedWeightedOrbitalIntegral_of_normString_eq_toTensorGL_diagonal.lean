-- Prove2me | Theorems.Thm_AutomorphicForm_eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal
-- name    : AutomorphicForm.eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/e83a4fa6-a065-58f1-821a-b6dcab47a32d
-- title:
--   Lift independence of local twisted weighted orbital integrals
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a Galois extension of $K$, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Let $v$ be a nonzero prime of $\mathcal{O}_K$, and let $\gamma \in GL_2(K_v)$ be regular semisimple in the sense that $(\mathrm{tr}\,\gamma)^2 - 4\det\gamma$ is a unit, with both off-diagonal entries of $\gamma$ equal to $0$. Let $\delta_1,\delta_2 \in GL_2(L \otimes_K K_v)$ both have norm string equal to the image of $\gamma$ under the entrywise map induced by $a \mapsto 1 \otimes a$, where the norm string of $\delta$ is the ordered product $\prod_{i=0}^{[L:K]-1}\sigma^{i}(\delta)$, $\sigma$ acting entrywise through $\sigma \otimes \mathrm{id}$. For $i = 1,2$ let $\tau'_i$ be a Haar measure, for the Borel structure on the subspace, on the $\sigma$-twisted centraliser $\{t : t\,\delta_i\,\sigma(t)^{-1} = \delta_i\}$ of $\delta_i$, normalised so that the preimage of the semi-local integral set — those $g \in GL_2(L \otimes_K K_v)$ with all entries of $g$ and of $g^{-1}$ in the image of the semi-local integers of $L$ at $v$ — has measure $1$. Let $\varphi_v : GL_2(L \otimes_K K_v) \to \mathbb{C}$ be locally constant with compact support, and let $J'_1, J'_2 \in \mathbb{C}$ be such that for each $i$ there is $s_i : GL_2(L \otimes_K K_v) \to \mathbb{R}$ satisfying the predicate `IsTwistedSectionFnOn` for the data $(\sigma,\delta_i,\tau'_i,\varphi_v)$ with $J'_i = \int \varphi_v(x^{-1}\delta_i\sigma(x))\, w(x)\, s_i(x)\, d\mu(x)$, the integral taken against the semi-local Haar measure $\mu$ on $GL_2(L \otimes_K K_v)$ and $w$ the semi-local weight, the finite sum over the extensions $w \mid v$ in $\mathcal{O}_L$ of the local weight of the component at $w$. Then $J'_1 = J'_2$.
--
--   This is the local statement, for a split regular diagonal norm at a finite place, that a twisted weighted orbital integral depends only on the norm $\gamma$ and not on the chosen lift $\delta$, on the normalised Haar measure on the twisted centraliser, or on the section function; it is the local input, in the style of Langlands' base change comparison for $GL(2)$, to the identification of twisted and untwisted weighted orbital terms. It is used by the statements that compute and compare twisted weighted orbital integrals for diagonal units at a place $v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (δ₁ δ₂ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₁ : AutomorphicForm.normString K L (v.adicCompletion K) σ δ₁ =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) γ)
    (hδ₂ : AutomorphicForm.normString K L (v.adicCompletion K) σ δ₂ =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) γ)
    (τ'₁ : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₁)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁))
    (hτ'₁ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁) τ'₁)
    (hτ'₁1 : τ'₁ (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (τ'₂ : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₂)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₂))
    (hτ'₂ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₂) τ'₂)
    (hτ'₂1 : τ'₂ (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv)
    (J'₁ J'₂ : ℂ) (hJ'₁ : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ δ₁ τ'₁ φv J'₁)
    (hJ'₂ : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ δ₂ τ'₂ φv J'₂) : J'₁ = J'₂ := by sorry
