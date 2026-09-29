-- Prove2me | Theorems.Thm_AutomorphicForm_convOp_mem_archCutSubmodule_of_isArchBiFinite_of_isAutomorphicFnAt
-- name    : AutomorphicForm.convOp_mem_archCutSubmodule_of_isArchBiFinite_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/d06d87cc-a59a-522e-9cb4-6720e60a733f
-- title:
--   Convolution by an arch-type-bi-finite test function stays in the arch cut
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the idele units $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated function $z\mapsto\xi_K(z)$ into $\mathbb{C}$ is continuous. Let $u:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfy `IsAutomorphicFnAt` for $\xi_K$ at the production pins attached to the data: domain the canonical truncation domain $\Phi_0$ of parameters $\alpha,\beta$, level subgroups $M\mapsto$ the intersection of the principal level at $M$ with the kernel of the archimedean projection, Hecke generators $v\mapsto$ `heckeGen`, and conditioning set the adelic box; these pins carry the Borel structure on $\mathrm{GL}_2(\mathbb{A}_K)$, the adelic Haar measure, central subgroup $\top$, and the adelic additive Haar measure conditioned on the box. Let $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous with compact support, let $\mathrm{tys}_K$ be an `ArchTypeFamily` for $K$ (for each infinite place $w$ a number $\mathrm{card}\,w$ of archimedean types $\mathrm{rep}\,w\,i$), and assume $f$ is arch-bi-finite for this family, i.e. $x\mapsto f(x^{-1})$ lies in the arch cut submodule and $f$ lies in the arch dual cut submodule. Then $\mathrm{convOp}_K(f)(u)$, the right convolution $\mathrm{rightConv}_K(u,f)$, lies in the arch cut submodule of $\mathrm{tys}_K$, namely the intersection over all infinite places $w$ of the sum over $i<\mathrm{card}\,w$ of the type submodules of $\mathrm{rep}\,w\,i$. The proof uses only the first half of the bi-finiteness hypothesis, that $x\mapsto f(x^{-1})$ lies in the arch cut submodule.
--
--   This is the smoothing step in the archimedean direction: convolving an automorphic function which is only known to be square-integrable on the canonical truncation domain with a compactly supported test function of prescribed archimedean types produces a function whose right translates by the maximal compact at each infinite place span representations of those types. It is used in the construction of smooth cuspidal automorphic functions from such $u$ and in the estimates comparing truncated inner products of $\mathrm{convOp}_K(f)(u)$ with those of $u$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_convOp_mem_archCutSubmodule_of_isArchBiFinite_of_isAutomorphicFnAt.lean

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

theorem AutomorphicForm.convOp_mem_archCutSubmodule_of_isArchBiFinite_of_isAutomorphicFnAt
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (u : AdelicGL2 (𝓞 K) K → ℂ) (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (tysK : ArchTypeFamily K) (_harch : IsArchBiFinite K tysK f) :
    convOp K f u ∈ archCutSubmodule K tysK := by sorry
