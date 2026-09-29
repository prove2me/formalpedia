-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain_of_continuous
-- name    : AutomorphicForm.continuous_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/6481635b-5878-5c74-b079-c2ec4b106473
-- title:
--   Continuity of right convolution of an automorphic L² function
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the idele unit group $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, whose induced complex-valued function $z \mapsto \xi_K(z)$ on $(\mathbb{A}_K)^\times$ is continuous. Let $u : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy the predicate `IsAutomorphicFnAt` for the character $\xi_K$ with respect to the package of carrier data `productionPinsOf` built from: the canonically chosen truncation domain $\Phi_0 =$ `canonicalTruncationDomain K α β` attached to $\alpha,\beta$; the assignment sending an ideal $M$ of $\mathcal{O}_K$ to the intersection of the principal level subgroup `principalLevel` at $M$ (the level-one subgroup at $M$ intersected with its conjugate by the Weyl element) with the kernel `finiteAdelicGL2Subgroup` of the archimedean projection $\mathrm{GL}_2(\mathbb{A}_K) \to \mathrm{GL}_2(\mathbb{A}_{K,\infty})$; the Hecke generators `heckeGen` at the finite places; and the adelic box, the latter entering through the conditioning of adelic additive Haar measure. The measure-theoretic data of the package are the Borel structure `glBorel` and the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$, and the central subgroup is $\top$. Let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous with compact support. Then `convOp K f u`, namely $x \mapsto \int_{\mathrm{GL}_2(\mathbb{A}_K)} u(xg) f(g)\,dg$ against `adelicGLHaar`, is continuous.
--
--   This is the standard fact that the right regular convolution operator $R(f)$ attached to a continuous compactly supported test function smooths an automorphic $L^2$ function to a continuous one. It feeds the estimates on $R(f)u$ used downstream, for instance the bounds on the $L^2$-norm of `convOp` over the canonical truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain_of_continuous.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.continuous_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain_of_continuous
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (u : AdelicGL2 (𝓞 K) K → ℂ) (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    Continuous (convOp K f u) := by sorry
