-- Prove2me | Theorems.Thm_AutomorphicForm_eLpNorm_convOp_le_ofReal_integral_norm_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
-- name    : AutomorphicForm.eLpNorm_convOp_le_ofReal_integral_norm_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/d328f141-dbab-5566-b16f-8692405ff844
-- title:
--   Young-type L² bound for right convolution on truncation domains
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the idele unit group $(\mathbf{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated scalar function $z\mapsto\xi_K(z)$ is continuous and has $\lVert\xi_K(z)\rVert=1$ for every $z$. Let $f:\mathrm{GL}_2(\mathbf{A}_K)\to\mathbb{C}$ be continuous with compact support, and let $u:\mathrm{GL}_2(\mathbf{A}_K)\to\mathbb{C}$ satisfy `IsAutomorphicFnAt`, i.e. the predicate `LsXiMember` with character $\xi_K$ for the carrier data `productionPinsOf` determined by: the Borel $\sigma$-algebra and Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbf{A}_K)$, the domain `canonicalTruncationDomain K α β` (the set component of the canonically chosen truncation datum for $\alpha,\beta$), the central subgroup $\top$, the level subgroups $M\mapsto\operatorname{principalLevel}(M)\sqcap\operatorname{finiteAdelicGL2Subgroup} K$ (the latter being the kernel of the archimedean projection `glArch`), the Hecke generators $\operatorname{heckeGen}$ at the finite places, and the additive Haar measure on $\mathbf{A}_K$ conditioned on the box `adelicBox K`. Then, writing $\operatorname{convOp} K f u:g\mapsto\int u(gx)f(x)\,dx$ for right convolution against $f$, the $L^2$ norm of $\operatorname{convOp} K f u$ for Haar measure restricted to `canonicalTruncationDomain K α β` is at most $\bigl(\int\lVert f(x)\rVert\,dx\bigr)$, as an element of $[0,\infty]$, times the $L^2$ norm of $u$ for the same restricted measure.
--
--   This is the Young-type operator bound for the right convolution operator $R(f)$ acting on automorphic functions, in the sharp form where the constant is the $L^1$ norm of $f$ rather than an unspecified one. It feeds the estimate [`AutomorphicForm.norm_setIntegral_convOp_mul_conj_sub_le_of_forall_norm_setIntegral_sub_mul_conj_le`](thm.html#AutomorphicForm.norm_setIntegral_convOp_mul_conj_sub_le_of_forall_norm_setIntegral_sub_mul_conj_le) in the analysis of the convolution action on the truncated $L^2$ space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eLpNorm_convOp_le_ofReal_integral_norm_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt.lean

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

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.eLpNorm_convOp_le_ofReal_integral_norm_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (u : AdelicGL2 (𝓞 K) K → ℂ)
    (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) :
    eLpNorm (convOp K f u) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
      ENNReal.ofReal (∫ x, ‖f x‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
        eLpNorm u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
