-- Prove2me | Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
-- name    : AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/761cb090-78ba-5d15-912c-28bbe77d0067
-- title:
--   Right convolution preserves automorphy at the truncation-domain pins
-- statement:
--   Let $K$ be a number field (with decidable equality on the height-one spectrum of $\mathcal{O}_K$), and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Let $\xi_K$ be a monoid homomorphism from the full subgroup $\top$ of the idele group $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, assumed continuous as the map $z\mapsto \xi_K(z)\in\mathbb{C}$ and unitary, $\|\xi_K(z)\|=1$ for all $z$. The relevant data are packaged by `productionPinsOf` for $K$ with domain $D$ the canonical truncation domain `canonicalTruncationDomain K α β` (the third component of the canonically chosen truncation datum for $\alpha,\beta$), level subgroups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, Hecke elements $v\mapsto$ `heckeGen (𝓞 K) K v`, and box `adelicBox K`; these pins carry the Borel $\sigma$-algebra `glBorel` and the Haar measure `adelicGLHaar` on $GL_2(\mathbb{A}_K)$, central subgroup $\top$, together with `adeleBorel` and the measure `adelicAddHaar` conditioned on `adelicBox K`. Given $u:GL_2(\mathbb{A}_K)\to\mathbb{C}$ satisfying the predicate `IsAutomorphicFnAt` for these pins and $\xi_K$, and $f:GL_2(\mathbb{A}_K)\to\mathbb{C}$ continuous with compact support, the conclusion is that `convOp K f u`, namely $g\mapsto\int u(gx)f(x)\,d\mu(x)$ for $\mu$ the adelic Haar measure, again satisfies `IsAutomorphicFnAt` for the same pins and $\xi_K$.
--
--   This is the statement that the right convolution operator $R(f)$, for $f$ continuous of compact support, acts on the space of automorphic functions with unitary central character $\xi_K$ attached to the canonical truncation domain: left invariance, $\xi_K$-equivariance and square-integrability over the truncation domain are all preserved. It is used in the subsequent study of $R(f)$ on principal-level invariants and on residual projections, and in the approximation of automorphic $L^2$ functions by continuous archimedean-finite ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain.lean

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
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (convOp K f u) := by sorry
