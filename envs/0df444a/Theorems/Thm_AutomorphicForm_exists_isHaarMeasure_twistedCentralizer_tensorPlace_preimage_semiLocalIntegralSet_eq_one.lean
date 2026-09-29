-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one
-- name    : AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e9c285b0-d359-52f8-ac3d-846e543075e8
-- title:
--   Haar measures on local twisted centralisers normalised on integral points
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite extension algebra over $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $\delta$ be an element of $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $K$. The assertion is the existence of a family $\tau f$ indexed by the finite places $v$ of $K$ (the height-one primes of $\mathcal{O}_K$) such that, for each $v$, $\tau f\,v$ is a measure, for the Borel $\sigma$-algebra of the subspace topology, on the $\sigma$-twisted centraliser of the local component $\delta_v :=$ `tensorPlace K L v δ`, the image of $\delta$ under the map of general linear groups induced by $\mathrm{id}_L \otimes (\mathbb{A}_K \to K_v)$; this twisted centraliser is the subgroup of $t \in \mathrm{GL}_2(L \otimes_K K_v)$ with $t\,\delta_v\,(\sigma_{\mathrm{GL}} t)^{-1} = \delta_v$, where $\sigma_{\mathrm{GL}}$ acts entrywise through $\sigma \otimes \mathrm{id}$ on $L \otimes_K K_v$. The family satisfies two conditions: each $\tau f\,v$ is a Haar measure, and each $\tau f\,v$ assigns mass $1$ to the preimage, under the inclusion of the twisted centraliser, of `semiLocalIntegralSet K L v`, the set of $g \in \mathrm{GL}_2(L \otimes_K K_v)$ such that both $g$ and $g^{-1}$ have all entries in the image of the semi-local integers $\mathcal{O}_L \otimes \mathcal{O}_{K_v}$ inside $L \otimes_K K_v$. No hypothesis is imposed on $\delta$.
--
--   This is the normalisation of local Haar measures used to define twisted orbital integrals on the $\sigma$-twisted centralisers occurring in the base-change comparison: at each finite place the measure is pinned down by giving mass one to the integral points of the centraliser. It is used in the bounds for orbital integrals over double cosets and in the construction of coupled twisted torus families of total mass one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one.lean

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
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    ∃ (τf : ∀ v : HeightOneSpectrum (𝓞 K),
        @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ))
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ))),
      (∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)) (τf v)) ∧
      (∀ v : HeightOneSpectrum (𝓞 K),
        τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) := by sorry
