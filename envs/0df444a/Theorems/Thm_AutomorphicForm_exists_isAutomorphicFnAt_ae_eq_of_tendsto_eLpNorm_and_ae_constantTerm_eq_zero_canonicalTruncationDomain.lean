-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isAutomorphicFnAt_ae_eq_of_tendsto_eLpNorm_and_ae_constantTerm_eq_zero_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_isAutomorphicFnAt_ae_eq_of_tendsto_eLpNorm_and_ae_constantTerm_eq_zero_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/04b99144-754c-5ab5-9da5-f93600f1e356
-- title:
--   L² limits of automorphic functions; cuspidality closed and linear
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta\in\mathbb R$ with $0<\alpha$ and $\alpha<\beta$, and let $\xi_K$ be a monoid homomorphism from the top subgroup of the idele units $(\mathbb A_K)^\times$ to $\mathbb C^\times$ whose associated function on $(\mathbb A_K)^\times$ is continuous and has constant absolute value $1$. Throughout, $\Phi_0 =$ `canonicalTruncationDomain K α β` is the truncation domain attached to $\alpha,\beta$, the measure on $GL_2(\mathbb A_K)$ is the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` for the Borel structure `glBorel`, and the carrier data are `productionPinsOf` applied to $\Phi_0$, to the levels $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, to the Hecke generators $v\mapsto$ `heckeGen (𝓞 K) K v`, and to the adelic box `adelicBox K` (the adeles with infinite part in `infiniteBox K` and finite part integral); these pins carry the Borel structure `adeleBorel` on $\mathbb A_K$, the full central subgroup $\top$, and the measure $\nu$ obtained by conditioning the adelic additive Haar measure on `adelicBox K`. Write $A$ for the predicate `IsAutomorphicFnAt K · ξ_K` (membership in `LsXiMember` for these pins and central character), and say that $u$ is almost everywhere cuspidal when `constantTerm ν unipotentGL2 u g = 0` for Haar-almost every $g\in GL_2(\mathbb A_K)$. The conclusion is the conjunction of three assertions. First, if $u_n$ all satisfy $A$, if $v\in L^2$ for the restriction of Haar measure to $\Phi_0$, and if the $L^2$-seminorms `eLpNorm (u_n - v) 2` over $\Phi_0$ tend to $0$, then there exists $U$ satisfying $A$ with $U = v$ almost everywhere on $\Phi_0$. Second, if in addition each $u_n$ is almost everywhere cuspidal and $v$ itself satisfies $A$, then $v$ is almost everywhere cuspidal. Third, if $v_1,v_2$ satisfy $A$ and are almost everywhere cuspidal, then for all $c_1,c_2\in\mathbb C$ the function $g\mapsto c_1v_1(g)+c_2v_2(g)$ is almost everywhere cuspidal.
--
--   These are the Hilbert-space facts underlying the cuspidal projection: the classes in $L^2(\Phi_0)$ of automorphic functions with almost everywhere vanishing constant term form a linear subspace closed under $L^2(\Phi_0)$-limits, and every $L^2(\Phi_0)$-limit of automorphic functions admits a genuinely automorphic representative. They are used in the construction of the residual projection on the truncation domain and in the spectral expansion of integrals against an orthonormal basis of the isotypic cuspidal submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isAutomorphicFnAt_ae_eq_of_tendsto_eLpNorm_and_ae_constantTerm_eq_zero_canonicalTruncationDomain.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isAutomorphicFnAt_ae_eq_of_tendsto_eLpNorm_and_ae_constantTerm_eq_zero_canonicalTruncationDomain
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    letI := adeleBorel (𝓞 K) K
    (∀ (useq : ℕ → AdelicGL2 (𝓞 K) K → ℂ) (v : AdelicGL2 (𝓞 K) K → ℂ),
      (∀ n, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (useq n)) →
      MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) →
      Filter.Tendsto (fun n => eLpNorm (useq n - v) 2
          ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)))
        Filter.atTop (nhds 0) →
      ∃ U : AdelicGL2 (𝓞 K) K → ℂ,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK U ∧
        U =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] v) ∧
    (∀ (useq : ℕ → AdelicGL2 (𝓞 K) K → ℂ) (v : AdelicGL2 (𝓞 K) K → ℂ),
      (∀ n, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (useq n)) →
      (∀ n, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 (useq n) g = 0) →
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v →
      Filter.Tendsto (fun n => eLpNorm (useq n - v) 2
          ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)))
        Filter.atTop (nhds 0) →
      ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 v g = 0) ∧
    (∀ (v₁ v₂ : AdelicGL2 (𝓞 K) K → ℂ) (c₁ c₂ : ℂ),
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v₁ →
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v₂ →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 v₁ g = 0) →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 v₂ g = 0) →
      ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 (fun g => c₁ * v₁ g + c₂ * v₂ g) g = 0) := by sorry
