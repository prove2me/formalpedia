-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
-- name    : AutomorphicForm.setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/aa106a86-f4ca-5768-93c9-6563b57f5109
-- title:
--   Adjointness of right convolution on the truncation domain
-- statement:
--   Let $K$ be a number field (with decidable equality on the height one spectrum of $\mathcal{O}_K$), and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the idele unit group $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ such that $z\mapsto \xi_K(z)$ is continuous as a complex-valued function and $\lVert \xi_K(z)\rVert=1$ for every $z$. Let $v,w\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ each satisfy `IsAutomorphicFnAt` for $\xi_K$ with respect to the pins `productionPinsOf` attached to the canonical truncation domain $\Phi_0=$ `canonicalTruncationDomain K α β`, the level family $N\mapsto$ `principalLevel` $\sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators $v\mapsto$ `heckeGen`, and the box `adelicBox`; by definition this is the predicate `LsXiMember` for the Borel structure `glBorel`, the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`, the centre subgroup $\top$, the character $\xi_K$ and the domain $\Phi_0$ (the remaining fields of the pins record, namely the level family, the Hecke generators and the conditioned additive measure on the box, are not referred to by this predicate). Let $f\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous with compact support. Then, with $\mu$ the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` and $(\mathrm{convOp}\,f\,u)(g)=\int u(gx)f(x)\,d\mu(x)$,
--   $$\int_{\Phi_0} v(g)\,\overline{(\mathrm{convOp}\,f\,w)(g)}\,d\mu(g)=\int_{\Phi_0} \bigl(\mathrm{convOp}\,(x\mapsto\overline{f(x^{-1})})\,v\bigr)(g)\,\overline{w(g)}\,d\mu(g).$$
--
--   This is the adjointness $R(f)^{*}=R(f^{*})$, with $f^{*}(x)=\overline{f(x^{-1})}$, for the Hermitian pairing of $\xi_K$-isotypic automorphic functions integrated over the canonical truncation domain. It is used where pairings against $R(f)$-images are transferred to pairings of the reflected-conjugate convolution, in particular in the vanishing statement for `convOp` on the truncation domain, in the estimate for integrals of $\mathrm{convOp}$-pairings, and in the comparison of $\mathrm{convOp}$ with the continuous projection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt.lean

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

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (v w : AdelicGL2 (𝓞 K) K → ℂ)
    (_hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v)
    (_hw : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK w)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, v g * conj (convOp K f w g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        convOp K (fun x => conj (f x⁻¹)) v g * conj (w g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
