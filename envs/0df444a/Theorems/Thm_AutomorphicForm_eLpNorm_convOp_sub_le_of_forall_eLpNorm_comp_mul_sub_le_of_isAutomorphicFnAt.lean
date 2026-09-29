-- Prove2me | Theorems.Thm_AutomorphicForm_eLpNorm_convOp_sub_le_of_forall_eLpNorm_comp_mul_sub_le_of_isAutomorphicFnAt
-- name    : AutomorphicForm.eLpNorm_convOp_sub_le_of_forall_eLpNorm_comp_mul_sub_le_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/8fc33588-6220-553b-becf-371f2a8d7dfd
-- title:
--   Approximate identity bound for R(f)v-v on a truncation domain
-- statement:
--   Let $K$ be a number field and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Let $\xi_K$ be a homomorphism from the full subgroup $\top \le (\mathbb{A}_K)^{\times}$ to $\mathbb{C}^{\times}$ such that $z \mapsto \xi_K(z)$ is continuous as a complex-valued function, $\xi_K$ is trivial on the image of $K^{\times}$ under the idele embedding, and $|\xi_K(z)|=1$ for all $z$. Let $v : GL_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy `IsAutomorphicFnAt`, i.e. the predicate `LsXiMember` for the character $\xi_K$ and the carrier data `productionPinsOf`: the Borel structure `glBorel` on $GL_2(\mathbb{A}_K)$, the Haar measure `adelicGLHaar`, the domain `canonicalTruncationDomain K α β` (the third component of a chosen truncation datum for $(\alpha,\beta)$), central subgroup $\top$, level subgroups $N \mapsto \mathrm{principalLevel}(N) \sqcap \ker(\mathrm{glArch})$ (where $\mathrm{principalLevel}(N)$ is $\mathrm{levelOne}(N)$ intersected with its conjugate by the Weyl element), Hecke generators `heckeGen`, and the adelic additive Haar measure conditioned on `adelicBox K`. Let $f$ be continuous with compact support and $\int f \, d\mu = 1$ for the Haar measure $\mu =$ `adelicGLHaar`, and let $\delta \ge 0$ be such that for every $x$ with $f(x) \ne 0$ the $L^2$-norm of $g \mapsto v(gx)-v(g)$ with respect to $\mu$ restricted to `canonicalTruncationDomain K α β` is at most $\delta$. Then the $L^2$-norm, over the same restricted measure, of $g \mapsto (\mathrm{convOp}\,K\,f\,v)(g) - v(g)$, where $\mathrm{convOp}\,K\,f\,v = \mathrm{rightConv}\,K\,v\,f$ is the right convolution of $v$ against $f$, is at most $\bigl(\int \|f\| \, d\mu\bigr)\,\delta$ (all norms and bounds read in $[0,\infty]$ via `eLpNorm` and `ENNReal.ofReal`).
--
--   This is the approximate-identity estimate for the right convolution operator $R(f)$ acting on an automorphic function, obtained from Minkowski's integral inequality in $L^2$ of the truncation domain. It feeds the construction of continuous, archimedeanly finite, principal-level smooth vectors approximating a given automorphic function in $L^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eLpNorm_convOp_sub_le_of_forall_eLpNorm_comp_mul_sub_le_of_isAutomorphicFnAt.lean

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

theorem AutomorphicForm.eLpNorm_convOp_sub_le_of_forall_eLpNorm_comp_mul_sub_le_of_isAutomorphicFnAt
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (v : AdelicGL2 (𝓞 K) K → ℂ)
    (_hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (_hf1 : ∫ x, f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
    (δ : ℝ) (_hδ : 0 ≤ δ)
    (_hclose : ∀ x : AdelicGL2 (𝓞 K) K, f x ≠ 0 →
      eLpNorm (fun g : AdelicGL2 (𝓞 K) K => v (g * x) - v g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ ENNReal.ofReal δ) :
    eLpNorm (fun g : AdelicGL2 (𝓞 K) K => convOp K f v g - v g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
      ENNReal.ofReal (∫ x, ‖f x‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * ENNReal.ofReal δ := by sorry
