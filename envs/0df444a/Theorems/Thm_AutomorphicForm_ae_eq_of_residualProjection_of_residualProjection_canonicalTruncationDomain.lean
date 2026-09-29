-- Prove2me | Theorems.Thm_AutomorphicForm_ae_eq_of_residualProjection_of_residualProjection_canonicalTruncationDomain
-- name    : AutomorphicForm.ae_eq_of_residualProjection_of_residualProjection_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/6b02cc9f-f820-5180-becb-53796aa53d1c
-- title:
--   Almost-everywhere uniqueness of residual projections on truncation domains
-- statement:
--   Fix a number field $K$ and reals $\alpha,\beta$ with $0<\alpha<\beta$, and let $\xi_K$ be a homomorphism from the full subgroup $\top$ of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$. All data are taken with respect to the pins `productionPinsOf` attached to $K$, whose domain is the canonical truncation domain $D=$ `canonicalTruncationDomain K α β` (the third component of the canonically chosen truncation datum for $(\alpha,\beta)$), whose measurable structure is the Borel structure `glBorel` on $GL_2(\mathbb{A}_K)$, whose measure is the Haar measure `adelicGLHaar`, whose level subgroups are $M\mapsto$ `principalLevel` $\sqcap$ `finiteAdelicGL2Subgroup`, whose Hecke elements are the `heckeGen` at the finite places, and whose additive datum is the adelic additive Haar measure conditioned on `adelicBox K`; the central character subgroup of these pins is $\top$. Let $\theta,p,p':GL_2(\mathbb{A}_K)\to\mathbb{C}$ each satisfy `IsAutomorphicFnAt` for these pins and $\xi_K$. Assume further, for each of $p$ and $p'$, that it is an $L^2$-limit on $D$ of automorphic elements of the residual span — the $\mathbb{C}$-span of the functions $g\mapsto\chi(\det g)$ for characters $\chi$ of $(\mathbb{A}_K)^\times$ with $\chi(z)^2=\xi_K(z)$ — and that $\int_D(\theta-p)\overline{h}$, respectively $\int_D(\theta-p')\overline{h}$, vanishes for every automorphic $h$ in that span. The conclusion is $p'=p$ almost everywhere for `adelicGLHaar` restricted to $D$. The proof uses none of these seven hypotheses on $\theta$, $p$ and $p'$.
--
--   This is the Hilbert-space uniqueness of the orthogonal projection onto the closure of the residual span, transcribed for the $\xi_K$-automorphic $L^2$ space on the canonical truncation domain. It is used in the existence-and-uniqueness statement [`AutomorphicForm.exists_residualProjection_mem_span_chiDet_principalLevel_archCutSubmodule_and_ae_eq_of_isAutomorphicFnAt`](thm.html#AutomorphicForm.exists_residualProjection_mem_span_chiDet_principalLevel_archCutSubmodule_and_ae_eq_of_isAutomorphicFnAt), which packages the residual projection of an automorphic function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ae_eq_of_residualProjection_of_residualProjection_canonicalTruncationDomain.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.ae_eq_of_residualProjection_of_residualProjection_canonicalTruncationDomain
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (θ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hθ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK θ)
    (p p' : AdelicGL2 (𝓞 K) K → ℂ)
    (_hp : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p) (_hp' : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p')
    (_hpc : (∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
          IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (p - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε))
    (_hpo : (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (θ g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0))
    (_hp'c : (∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
          IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (p' - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε))
    (_hp'o : (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (θ g - p' g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)) :
    p' =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] p := by sorry
