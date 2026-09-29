-- Prove2me | Theorems.Thm_AutomorphicForm_mem_archCutSubmodule_of_mem_span_chiDet_principalLevel_of_residualProjection
-- name    : AutomorphicForm.mem_archCutSubmodule_of_mem_span_chiDet_principalLevel_of_residualProjection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/fb3be9c4-4a7d-5012-81c3-be216e2bdfa9
-- title:
--   Good-line combination orthogonal to the residual span lies in the cut
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta$ be reals with $0<\alpha<\beta$. Let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the idele units $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ which is continuous, takes the value $1$ on the image of $K^\times$, and is unitary ($\|\xi_K(z)\|=1$ for all $z$). Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let `tysK` be an `ArchTypeFamily` for $K$, that is, a cardinality function $w\mapsto \mathrm{card}(w)$ on the infinite places together with archimedean representation types $\mathrm{rep}(w,i)$ for $i<\mathrm{card}(w)$, and let $\theta:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfy: $\theta$ is automorphic in the sense of `IsAutomorphicFnAt` for the production pin data consisting of the canonical truncation domain $\Phi_0=$ `canonicalTruncationDomain K α β`, the level subgroups $M\mapsto$ `principalLevel` $M$ intersected with the kernel `finiteAdelicGL2Subgroup` of the archimedean projection, the local Hecke generators `heckeGen`, the box `adelicBox`, the Haar measure `adelicGLHaar` and central character $\xi_K$ on $\top$; $\theta(gu')=\theta(g)$ for all $g$ and all $u'$ in `principalLevel` $N\sqcap$ `finiteAdelicGL2Subgroup`; and $\theta$ lies in `archCutSubmodule K tysK`, the infimum over infinite places $w$ of the supremum over $i<\mathrm{card}(w)$ of the type submodules `archTypeSubmoduleAt K w (rep w i)`. Then, with the Borel structure on the adeles, for every $p:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$: if $p$ lies in the $\mathbb{C}$-span of the functions $g\mapsto\chi(\det g)$ for those characters $\chi$ of $(\mathbb{A}_K)^\times$ with $\chi^2=\xi_K$ on all of $\top$, $\chi$ trivial on principal ideles, $\chi$ continuous, and $\chi(\det u)=1$ for all $u$ in `principalLevel` $N\sqcap$ `finiteAdelicGL2Subgroup`, and if for every $h$ which is automorphic for the same pin data and lies in `residualSpan`, the span of the functions $g\mapsto\chi'(\det g)$ with $\chi'^2=\xi_K$, one has $\int_{\Phi_0}(\theta-p)\overline{h}\,d(\mathrm{adelicGLHaar})=0$, then $p$ lies in `archCutSubmodule K tysK`.
--
--   This is the step showing that the component of a typed automorphic form along the one-dimensional "good lines" $\chi\circ\det$ of level $N$ is itself of the prescribed archimedean type, the orthogonality hypothesis identifying $p$ as the residual projection of $\theta$. It is used in the construction of the residual projection of an automorphic form lying in the archimedean cut, via [`AutomorphicForm.exists_residualProjection_mem_span_chiDet_principalLevel_archCutSubmodule_and_ae_eq_of_isAutomorphicFnAt`](thm.html#AutomorphicForm.exists_residualProjection_mem_span_chiDet_principalLevel_archCutSubmodule_and_ae_eq_of_isAutomorphicFnAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_archCutSubmodule_of_mem_span_chiDet_principalLevel_of_residualProjection.lean

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

theorem AutomorphicForm.mem_archCutSubmodule_of_mem_span_chiDet_principalLevel_of_residualProjection
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K)
    (θ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hθ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK θ)
    (_hθN : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, θ (g * u') = θ g)
    (_hθt : θ ∈ archCutSubmodule K tysK) :
    letI := adeleBorel (𝓞 K) K
    ∀ (p : AdelicGL2 (𝓞 K) K → ℂ),
      p ∈ Submodule.span ℂ ((fun χ => chiDet (𝓞 K) K χ) '' {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) ∧
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, χ (Matrix.GeneralLinearGroup.det u) = 1}) →
      (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (θ g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
      p ∈ archCutSubmodule K tysK := by sorry
