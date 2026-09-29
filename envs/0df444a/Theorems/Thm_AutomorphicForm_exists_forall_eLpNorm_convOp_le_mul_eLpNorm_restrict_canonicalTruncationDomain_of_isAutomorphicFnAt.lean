-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_convOp_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
-- name    : AutomorphicForm.exists_forall_eLpNorm_convOp_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/200b3ba1-4e19-5218-aaef-7f517fbb9815
-- title:
--   L² boundedness of right convolution on the truncation domain
-- statement:
--   Let $K$ be a number field and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Let $\xi_K$ be a homomorphism from the full subgroup $\top$ of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated function $z\mapsto\xi_K(z)$ on $(\mathbb{A}_K)^\times$ is continuous and takes values of modulus $1$, and let $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous with compact support. Then there is a real $c\ge 0$ such that for every $u:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfying `IsAutomorphicFnAt` for the character $\xi_K$ and the carrier data `productionPinsOf` built from the canonical truncation domain $\Phi_0=$ `canonicalTruncationDomain K α β` (the set component of the classically chosen truncation datum for $\alpha,\beta$, empty if none exists), the level subgroups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen (𝓞 K) K v`, and the adelic box `adelicBox K` — that is, membership in the space cut out by `LsXiMember` for the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the centre $\top$, the character $\xi_K$, the domain $\Phi_0$, and the adelic Haar measure conditioned on `adelicBox K` — one has $$\|R(f)u\|_{L^2(\mu|_{\Phi_0})}\le c\,\|u\|_{L^2(\mu|_{\Phi_0})},$$ where $R(f)u(g)=\int u(gx)f(x)\,d\mu(x)$ is `convOp K f u` and $\mu$ is the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is the quantitative operator-norm statement for right convolution by a test function on the $\xi$-isotypic automorphic $L^2$ space, read on the canonical truncation domain: the constant depends only on $f$ and is uniform over automorphic $u$. It is used in the construction of the residual projection and in the Parseval-type expansion of $\int\bar u\,R(f)u$ over an orthonormal family in the isotypic cuspidal submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_eLpNorm_convOp_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt.lean

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

theorem AutomorphicForm.exists_forall_eLpNorm_convOp_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ u : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
      eLpNorm (convOp K f u) 2
          ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
        ENNReal.ofReal c *
          eLpNorm u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
