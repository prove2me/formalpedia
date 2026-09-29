-- Prove2me | Theorems.Thm_AutomorphicForm_convOp_residualProjection_of_residualProjection
-- name    : AutomorphicForm.convOp_residualProjection_of_residualProjection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/3233163e-b33f-525c-bbb4-d56c46c10494
-- title:
--   Right convolution preserves the residual projection property
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and write $\Phi_0=$ `canonicalTruncationDomain K α β` for the canonical truncation domain in $\mathrm{GL}_2(\mathbb{A}_K)$ and $\mu=$ `adelicGLHaar (Fin 2) (𝓞 K) K` for the adelic Haar measure on that group (with its Borel structure `glBorel`). Let $\xi_K$ be a homomorphism from the full group of idele units $(\mathbb{A}_K)^\times$ (presented as the subgroup $\top$) to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function, trivial on the image of $K^\times$ under `Units.map` of `algebraMap`, and of absolute value $1$ at every point. Let $f$ be a continuous, compactly supported complex function on $\mathrm{GL}_2(\mathbb{A}_K)$, and let $\theta,p$ be complex functions on $\mathrm{GL}_2(\mathbb{A}_K)$. Throughout, automorphy means the predicate `IsAutomorphicFnAt` for the carrier pins `productionPinsOf` built from the domain $\Phi_0$, the measure $\mu$, the central subgroup $Z=\top$, the levels $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen (𝓞 K) K v` and the box `adelicBox K`, together with the character $\xi_K$; and the residual span is the $\mathbb{C}$-subspace spanned by the functions $\chi\circ\det$ for homomorphisms $\chi:(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ with $\chi(z)^2=\xi_K(z)$ for all $z$. The hypotheses are that $\theta$ and $p$ are automorphic in this sense, that $p$ is an $L^2$-limit of automorphic members of the residual span (for every $\varepsilon>0$ there is an automorphic $q$ in the residual span with `eLpNorm` of $p-q$ at exponent $2$ for $\mu$ restricted to $\Phi_0$ less than $\varepsilon$), and that $\int_{\Phi_0}(\theta-p)\overline{h}\,d\mu=0$ for every automorphic $h$ in the residual span. The conclusion is the conjunction of the three corresponding assertions for the right convolution $R(f)p=$ `convOp K f p` $=$ `rightConv K p f`: it is automorphic, it is an $L^2(\Phi_0)$-limit of automorphic members of the residual span in the same $\varepsilon$-sense, and $\int_{\Phi_0}\bigl(R(f)\theta-R(f)p\bigr)\overline{h}\,d\mu=0$ for every automorphic $h$ in the residual span.
--
--   This records that right convolution by a test function commutes with the orthogonal projection onto the closure of the residual span in $L^2(\Phi_0)$: it transports the three-clause characterisation of the residual projection of $\theta$ to the residual projection of $R(f)\theta$. It is used in the computation of pairings of pseudo-Eisenstein functions against their convolutes, in the statements [`AutomorphicForm.setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay`](thm.html#AutomorphicForm.setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay) and [`AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_convOp_pseudoEisenstein_sub_eq_mul_sum_integral_axis_pairing_convOp_of_paleyWiener`](thm.html#AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_convOp_pseudoEisenstein_sub_eq_mul_sum_integral_axis_pairing_convOp_of_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_convOp_residualProjection_of_residualProjection.lean

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

theorem AutomorphicForm.convOp_residualProjection_of_residualProjection
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (θ p : AdelicGL2 (𝓞 K) K → ℂ)
    (_hθ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK θ)
    (_hp : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p)
    (_hpc : ∀ ε > (0:ℝ), ∃ q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q ∧
        eLpNorm (p - q) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
    (_hpo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (θ g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) :
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (convOp K f p) ∧
    (∀ ε > (0:ℝ), ∃ q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q ∧
        eLpNorm (convOp K f p - q) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε) ∧
    (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          (convOp K f θ g - convOp K f p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) := by sorry
