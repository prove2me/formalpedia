-- Prove2me | Theorems.Thm_AutomorphicForm_exists_residualProjection_mem_span_chiDet_principalLevel_of_isAutomorphicFnAt
-- name    : AutomorphicForm.exists_residualProjection_mem_span_chiDet_principalLevel_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/f3d225f4-4899-58f0-a13b-a2fdab352560
-- title:
--   Residual projection onto the level-N good lines
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha<\beta$, and let $\xi_K$ be a homomorphism from the full subgroup $\top$ of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function, trivial on the image of $K^\times$ under the unit map of $K\to\mathbb{A}_K$, and unitary ($\|\xi_K(z)\|=1$ for all $z$). Let $N$ be a nonzero ideal of $\mathcal{O}_K$ and $\theta:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$. The data fixed throughout is the production pins for $K$ with truncation domain $\Phi_0=$ `canonicalTruncationDomain K α β`, level subgroups $M\mapsto$ `principalLevel` $(M)$ intersected with the kernel of the archimedean projection of $\mathrm{GL}_2(\mathbb{A}_K)$, Hecke generators $v\mapsto$ `heckeGen`, and box `adelicBox`; for these pins the central subgroup is $\top$, the measure is the adelic Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ and the domain is $\Phi_0$. Assume $\theta$ satisfies `IsAutomorphicFnAt` for these pins and $\xi_K$ (the membership predicate `LsXiMemberAt` for that data) and is right invariant under $U(N)=$ `principalLevel` $(N)\sqcap$ the kernel of the archimedean projection. The conclusion asserts the existence of $p:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ such that: $p$ satisfies the same automorphy predicate; for every $\varepsilon>0$ there is $r$ in the residual span — the $\mathbb{C}$-span of the functions $\chi\circ\det$ for characters $\chi$ of $\mathbb{A}_K^\times$ with $\chi^2=\xi_K$ on $\top$ — which itself satisfies the automorphy predicate and has $\|p-r\|_{L^2}<\varepsilon$ for the Haar measure restricted to $\Phi_0$; for every $h$ in the residual span satisfying the automorphy predicate, $\int_{\Phi_0}(\theta-p)\overline{h}\,d\mu=0$; moreover $p$ lies in the $\mathbb{C}$-span of the functions $\chi\circ\det$ as $\chi$ runs over those characters with $\chi^2=\xi_K$, $\chi$ trivial on the image of $K^\times$, $\chi$ continuous, and $\chi(\det u)=1$ for all $u\in U(N)$; and finally $p$ is continuous, `IsArchKFinite` (archimedean $K$-finite at every infinite place) and right $U(N)$-invariant.
--
--   This is the construction of the residual (one-dimensional, $\chi\circ\det$) part of an automorphic function of principal level $N$: the orthogonal projection of $\theta$ onto the residual span is realised inside the span of the finitely many characters $\chi$ with $\chi^2=\xi_K$ that are continuous, trivial on $K^\times$ and trivial on $\det U(N)$. It feeds the refinement of the same statement incorporating the archimedean cut submodule and an almost-everywhere identification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_residualProjection_mem_span_chiDet_principalLevel_of_isAutomorphicFnAt.lean

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

theorem AutomorphicForm.exists_residualProjection_mem_span_chiDet_principalLevel_of_isAutomorphicFnAt
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (θ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hθ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK θ)
    (_hθN : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, θ (g * u') = θ g) :
    letI := adeleBorel (𝓞 K) K
    ∃ (p : AdelicGL2 (𝓞 K) K → ℂ),
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p ∧
      ((∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
          IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (p - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε) ∧
        (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (θ g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)) ∧
      p ∈ Submodule.span ℂ ((fun χ => chiDet (𝓞 K) K χ) '' {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) ∧
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, χ (Matrix.GeneralLinearGroup.det u) = 1}) ∧
      Continuous p ∧ IsArchKFinite K p ∧
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, p (g * u') = p g) := by sorry
