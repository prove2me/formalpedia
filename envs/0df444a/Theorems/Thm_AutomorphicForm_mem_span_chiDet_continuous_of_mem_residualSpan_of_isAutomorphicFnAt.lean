-- Prove2me | Theorems.Thm_AutomorphicForm_mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt
-- name    : AutomorphicForm.mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/56a15df8-ee46-5b05-addf-eb7df45787ee
-- title:
--   Residual members are spanned by continuous characters χ∘det
-- statement:
--   Let $K$ be a number field and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Let $\xi_K$ be a monoid homomorphism from the full subgroup $\top$ of the idele units $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated $\mathbb{C}$-valued function $z\mapsto\xi_K(z)$ is continuous, and let $r$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_K)$. Write $P$ for the carrier pins `productionPinsOf` attached to $K$ with domain the canonical truncation domain `canonicalTruncationDomain K α β`, level subgroups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, Hecke generators $v\mapsto$ `heckeGen (𝓞 K) K v` and box `adelicBox K`; thus $P$ carries the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the central subgroup $\top$, and the Haar measure on $\mathbb{A}_K$ conditioned on the adelic box. Assume $r$ lies in the residual span for $\top$ and $\xi_K$, that is, in the $\mathbb{C}$-span of the functions $g\mapsto\chi(\det g)$ for monoid homomorphisms $\chi\colon(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ with $\chi(z)^2=\xi_K(z)$ for all $z$, and that $r$ satisfies `IsAutomorphicFnAt` for $P$ and $\xi_K$, the predicate `LsXiMember` for the Borel structure, Haar measure, subgroup $\top$ with character $\xi_K$ and domain `canonicalTruncationDomain K α β` recorded in $P$. Then $r$ lies in the $\mathbb{C}$-span of the functions $g\mapsto\chi(\det g)$ where $\chi$ runs over those monoid homomorphisms $(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ which satisfy $\chi(z)^2=\xi_K(z)$ for all $z$, are trivial on the image of $K^\times$ under $\mathrm{Units.map}$ of $K\to\mathbb{A}_K$, and are continuous as $\mathbb{C}$-valued functions.
--
--   This is the bridge from the purely algebraic residual span, formed over arbitrary (possibly discontinuous) characters of the idele group, to the residual lines actually occurring in the analytic theory: continuous Hecke characters trivial on the principal ideles whose square is the prescribed central character. It is used downstream in the analysis of the residual projection and of orthogonality relations against pseudo-Eisenstein kernels on the truncated domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (r : AdelicGL2 (𝓞 K) K → ℂ)
    (_hr : r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK)
    (_hra : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r) :
    r ∈ Submodule.span ℂ ((fun χ => chiDet (𝓞 K) K χ) '' {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}) := by sorry
