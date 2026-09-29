-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_isAutomorphicFnAt_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_isAutomorphicFnAt_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/d206b57a-397f-5810-bc63-02fc74235a44
-- title:
--   Strong L²-continuity of right translation at the identity
-- statement:
--   Let $K$ be a number field and let $G = GL_2(\mathbb{A}_K)$ be the general linear group of degree $2$ over the adele ring of $K$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`. Fix reals $\alpha, \beta$ with $0 < \alpha < \beta$, and let $\Phi_0 =$ `canonicalTruncationDomain K α β` be the canonically chosen truncation domain attached to $\alpha,\beta$, i.e. the third component of a datum satisfying `IsTruncationDatum` selected by choice (and $\emptyset$ if no such datum exists). Let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the idele unit group $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function of the idele, trivial on the image of $K^\times$ under the map induced by $K \to \mathbb{A}_K$, and unitary, $\|\xi_K(z)\| = 1$ for all $z$. Let $v : G \to \mathbb{C}$ satisfy `IsAutomorphicFnAt`, that is the predicate `LsXiMember` for the character $\xi_K$ and the bundle of data `productionPinsOf` consisting of: the Borel structure and Haar measure on $G$, the domain $\Phi_0$, the central subgroup $\top$, the level subgroups $M \mapsto$ `principalLevel` $(M)\cap\ker($`glArch`$)$, the Hecke elements $\mathfrak{v} \mapsto$ `heckeGen` $\mathfrak{v}$, and the additive Haar measure on $\mathbb{A}_K$ conditioned on the adelic box `adelicBox K`. Then for every $\varepsilon > 0$ there is a neighbourhood $U$ of $1$ in $G$ such that for all $x \in U$ the $L^2$-norm of $g \mapsto v(gx) - v(g)$, taken with respect to the Haar measure of $G$ restricted to $\Phi_0$, is less than $\varepsilon$.
--
--   This is the strong continuity at the identity of the right regular representation on the automorphic $L^2$-space of the canonical truncation domain, with $\varepsilon$ and the neighbourhood made explicit. It is the analytic input to the density of smooth vectors, used by [`AutomorphicForm.exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt`](thm.html#AutomorphicForm.exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_isAutomorphicFnAt_canonicalTruncationDomain.lean

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

theorem AutomorphicForm.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_isAutomorphicFnAt_canonicalTruncationDomain
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
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ nhds (1 : AdelicGL2 (𝓞 K) K), ∀ x ∈ U,
      eLpNorm (fun g : AdelicGL2 (𝓞 K) K => v (g * x) - v g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε := by sorry
