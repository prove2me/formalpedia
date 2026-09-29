-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/e24f8c5a-2e76-5a51-aacf-eaed15487981
-- title:
--   Residual projection on the canonical truncation domain
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the idele units $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function, trivial on the image of $K^\times$ under `Units.map` of $K \to \mathbb{A}_K$, and unitary, $\|\xi_K(z)\|=1$ for all $z$. Throughout, automorphy means the predicate `IsAutomorphicFnAt` for the production pins `productionPinsOf` built from the domain $\Phi_0 =$ `canonicalTruncationDomain K α β`, the level subgroups $M \mapsto$ `principalLevel (𝓞 K) K M` intersected with `finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen (𝓞 K) K v`, and the box `adelicBox K`; it is the condition `LsXiMember` taken with respect to the Borel structure on $\mathrm{GL}_2(\mathbb{A}_K)$, the measure `adelicGLHaar`, the centre $\top$ with character $\xi_K$, and the domain $\Phi_0$. Given $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ automorphic in this sense, the conclusion, formed with the Borel structure `adeleBorel` on $\mathbb{A}_K$, asserts the existence of $p : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ such that: $p$ is automorphic; for every $\varepsilon>0$ there is an automorphic $r$ lying in `residualSpan`, the $\mathbb{C}$-span of the functions $g \mapsto \chi(\det g)$ for characters $\chi$ of $(\mathbb{A}_K)^\times$ with $\chi(z)^2=\xi_K(z)$ for all $z$, with `eLpNorm` of $p-r$ in $L^2$ of Haar measure restricted to $\Phi_0$ less than $\varepsilon$; and for every automorphic $h$ in `residualSpan`, $\int_{\Phi_0} (f-p)\overline{h}\, d\mu = 0$.
--
--   This is the Hilbert-space orthogonal projection of an $L^2$ automorphic function on the truncated domain onto the closure of the automorphic residual functions (the span of the characters $\chi \circ \det$ with $\chi^2 = \xi$ on the centre), together with the choice of an automorphic representative of the projection. It is used in the pseudo-Eisenstein and Paley–Wiener matching statements, where the residual part must be subtracted before the cuspidal estimates are applied.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain.lean

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

theorem AutomorphicForm.exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (_hf : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK f) :
    letI := adeleBorel (𝓞 K) K
    ∃ (p : AdelicGL2 (𝓞 K) K → ℂ),
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p ∧
      (∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
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
            (f g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) := by sorry
