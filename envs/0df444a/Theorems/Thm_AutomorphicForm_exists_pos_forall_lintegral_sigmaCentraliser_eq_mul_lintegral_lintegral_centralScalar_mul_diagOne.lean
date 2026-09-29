-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne
-- name    : AutomorphicForm.exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/8dcf32cc-77e5-5ce2-9211-f03944baa486
-- title:
--   Haar measure on the twisted diagonal centraliser in GL₂(A_L)
-- statement:
--   Let $L/K$ be an extension of number fields which is Galois, let $D$ be an idelic Galois descent datum for $L/K$ — a monoid homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, each automorphism continuous and extending the action on $L$ through the structure map — and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the subgroup of integer powers of $\sigma$. Let $H$ be a closed subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ whose elements are exactly the $h$ with vanishing $(1,0)$ and $(0,1)$ entries for which $\sigma$, acting entrywise through $D$, satisfies $\sigma_D(h)h^{-1} \in Z(\mathrm{GL}_2(\mathbb{A}_L))$; let $\mu_H$ be a measure on $H$ that is both a (left) Haar measure and right invariant, and let $\nu_{Z_L}$, $\nu_K$ be Haar measures on the idele groups $\mathbb{A}_L^\times$, $\mathbb{A}_K^\times$ with their Borel structures. Let $\theta : \mathbb{A}_K^\times \to \mathbb{A}_L^\times$ be a continuous injective group homomorphism such that the idele norm (the value of the distributive Haar character on the adele ring) satisfies $\|\theta a\|_L = \|a\|_K^{[L:K]}$, such that $\theta$ carries the principal idele of $k \in K^\times$ to the principal idele of its image in $L$, and such that the fixed points of the induced action of $\sigma$ on $\mathbb{A}_L^\times$ are precisely the range of $\theta$. Then there exists a real $c_H > 0$ such that for every measurable $f : \mathrm{GL}_2(\mathbb{A}_L) \to [0,\infty]$ (for the Borel structure coming from the topology of $\mathrm{GL}_2(\mathbb{A}_L)$), $$\int_H f(h)\,d\mu_H = c_H \int_{\mathbb{A}_L^\times} \int_{\mathbb{A}_K^\times} f\bigl(z I_2 \cdot \mathrm{diag}(\theta a, 1)\bigr)\,d\nu_K(a)\,d\nu_{Z_L}(z),$$ the integrals being lower Lebesgue integrals of $[0,\infty]$-valued functions, with the scalar matrix $zI_2$ given by `centralScalar` and $\mathrm{diag}(\theta a,1)$ by `diagOne`.
--
--   This is the Haar-measure comparison for the $\sigma$-twisted centraliser of the diagonal torus: the map $(z,a) \mapsto z I_2 \cdot \mathrm{diag}(\theta a, 1)$ identifies $\mathbb{A}_L^\times \times \mathbb{A}_K^\times$ with $H$, so that the pushforward of the product of idelic Haar measures is proportional to the Haar measure of $H$. It supplies the normalising constant used in the subsequent comparisons of orbital and Hecke-type integrals over this twisted torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_pos_forall_lintegral_sigmaCentraliser_eq_mul_lintegral_lintegral_centralScalar_mul_diagOne
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ) (hθi : Function.Injective θ)
    (hθn : ∀ a, NumberField.TateGlobal.ideleNorm L (θ a) = NumberField.TateGlobal.ideleNorm K a ^ Module.finrank K L)
    (hθc : ∀ k : Kˣ, θ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (algebraMap K L : K →* L) k))
    (hθr : ∀ b : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ b = b ↔ b ∈ Set.range θ) :
    ∃ cH : ℝ, 0 < cH ∧ ∀ f : AdelicGL2 (𝓞 L) L → ENNReal, Measurable f →
      ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH =
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL := by sorry
