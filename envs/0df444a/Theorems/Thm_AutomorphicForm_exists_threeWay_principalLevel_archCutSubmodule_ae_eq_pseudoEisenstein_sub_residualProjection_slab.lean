-- Prove2me | Theorems.Thm_AutomorphicForm_exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab
-- name    : AutomorphicForm.exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/0d1c4652-0fa4-542f-9eaa-903cd4348004
-- title:
--   Three-way slab decomposition of a pseudo-Eisenstein series
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$, and let $\xi_K$ be a homomorphism from the full group of ideles $(\mathbb{A}_K)^\times$ (taken as the top subgroup) to $\mathbb{C}^\times$ which is continuous, unitary, and trivial on the image of $K^\times$. Let $N\neq 0$ be an ideal of $\mathcal O_K$ and $\mathcal T$ an archimedean type family, i.e. a finite list of representations of the row-isometry subgroup at each infinite place, cutting out the submodule $\mathrm{archCutSubmodule}$ (the intersection over infinite places of the span of the corresponding type submodules). All automorphy below is taken with respect to the pins `productionPinsOf` with domain the canonical truncation domain $\Phi_0=\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta$, adelic Haar measure on $\mathrm{GL}_2$, central subgroup $\top$ and character $\xi_K$, level groups $M\mapsto \mathrm{principalLevel}(M)\sqcap \mathrm{finiteAdelicGL2Subgroup}$, Hecke generators $\mathrm{heckeGen}_v$, and adelic box; the constant term of a function $h$ is $g\mapsto\int h(u(x)g)$ against the additive adelic Haar measure conditioned to the adelic box, $u(x)$ the unipotent matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Suppose $\psi$ is a slab profile for $\xi_K$: measurable, invariant under left translation by unipotents and by global Borel points, transforming by $\xi_K$ under central adelic scalars, bounded on each band $\|\det g\|\in[d_1,d_2]$ with $d_1>0$, and vanishing outside a band of adelic heights. Suppose its pseudo-Eisenstein series $\theta_\psi(g)=\psi(g)+\sum_{b\in K}\psi(w\,u(b)\,g)$ is invariant under right multiplication by $\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$ and lies in the archimedean cut of $\mathcal T$. Suppose $p_\psi$ is automorphic at these pins, is an $L^2(\Phi_0)$-limit of automorphic members of the residual span (the complex span of the functions $g\mapsto\chi(\det g)$ with $\chi^2=\xi_K$ on the central subgroup), and is such that $\theta_\psi-p_\psi$ is orthogonal over $\Phi_0$ to every automorphic member of the residual span. Then there exist $u_c,u_r,u_e$, all automorphic at these pins, together with: a.e. vanishing of the constant term of $u_c$; $L^2(\Phi_0)$-approximability of $u_r$ by automorphic members of the residual span; vanishing of $\int_{\Phi_0}u_e\overline h$ for every automorphic $h$ whose constant term vanishes a.e. or which lies in the residual span; and $\theta_\psi=u_c+u_r+u_e$ almost everywhere on $\Phi_0$; such that, in addition, $u_e$ is invariant under right multiplication by $\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, lies in the archimedean cut of $\mathcal T$, and equals $\theta_\psi-p_\psi$ almost everywhere on $\Phi_0$.
--
--   This is the bookkeeping form, on a truncated determinant slab and at principal level $N$ with a prescribed archimedean type, of the splitting of a pseudo-Eisenstein series into cuspidal, residual and remaining parts, with the last part identified almost everywhere with $\theta_\psi$ minus its residual projection. It is invoked, once for each of two profiles, by [`AutomorphicForm.exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab.lean

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

theorem AutomorphicForm.exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hψ : AutomorphicForm.IsSlabProfile K
      (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)).Z ξK ψ)
    (_hθN : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, AutomorphicForm.pseudoEisenstein K ψ (g * u') = AutomorphicForm.pseudoEisenstein K ψ g)
    (_hθt : AutomorphicForm.pseudoEisenstein K ψ ∈ archCutSubmodule K tysK)
    (pψ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hpψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK pψ)
    (_hpψc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)).Z ξK,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK r ∧ eLpNorm (pψ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
    (_hpψo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK h →
      h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)).Z ξK →
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) :
    letI := adeleBorel (𝓞 K) K
    ∃ (uc ur ue : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc) (_huc0 : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc g = 0))
      (_hur : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur)
      (_hurc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue)
      (_hueo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum : AutomorphicForm.pseudoEisenstein K ψ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc + ur + ue),
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ue (g * u') = ue g) ∧
    ue ∈ archCutSubmodule K tysK ∧
    ue =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))]
      (fun g => AutomorphicForm.pseudoEisenstein K ψ g - pψ g) := by sorry
