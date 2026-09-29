-- Prove2me | Theorems.Thm_AutomorphicForm_ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact
-- name    : AutomorphicForm.ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/2a88ac12-2442-57b7-a212-946cc4a72686
-- title:
--   Compact kernel averages: a.e. additivity and an L² bound
-- statement:
--   Let $K$ be a number field and $\alpha<\beta$ reals with $0<\alpha$. Let $\xi_K$ be a group homomorphism from the full subgroup $\top$ of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ which, viewed as a $\mathbb{C}$-valued function on the ideles, is continuous, takes the value $1$ on the image of $K^\times$ under `Units.map` of the structure map, and has absolute value $1$ everywhere. The adeles carry the Borel $\sigma$-algebra `adeleBorel`. Then for every continuous function $\kappa$ on the subgroup `adelicMaximalCompact K` of $\mathrm{GL}_2(\mathbb{A}_K)$ consisting of those $k$ whose finite component lies in `finiteIntegralGL2` and whose component at each infinite place is a row isometry, every operator $P$ on functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfying $P\varphi(g)=\int \kappa(k)\,\varphi(gk)\,d(\mathrm{maximalCompactHaar}\,K)$ for all $\varphi$ and $g$, and all $\varphi,\psi$ satisfying `IsAutomorphicFnAt` for the character $\xi_K$ and the pins `productionPinsOf` built from the domain `canonicalTruncationDomain K` $\alpha$ $\beta$, the level subgroups $M\mapsto$ `principalLevel` $\sqcap$ `finiteAdelicGL2Subgroup` (the kernel of the archimedean projection `glArch`), the Hecke generators `heckeGen`, and the box `adelicBox K` (so the measurable structure is `glBorel`, the measure `adelicGLHaar`, the central subgroup $\top$, and the additive measure the conditioning of `adelicAddHaar` on that box), three assertions hold, with $\mu$ denoting `adelicGLHaar (Fin 2) (𝓞 K) K` restricted to `canonicalTruncationDomain K` $\alpha$ $\beta$: for $\mu$-almost every $g$ the function $k\mapsto \kappa(k)\varphi(gk)$ is integrable for `maximalCompactHaar K`; for $\mu$-almost every $g$ one has $P(\varphi-\psi)(g)=P\varphi(g)-P\psi(g)$; and the $L^2(\mu)$-seminorm of $P\varphi$ is at most $\mathrm{ofReal}\big(\int\|\kappa\|\big)$ times that of $\varphi$.
--
--   This is the Minkowski-type estimate for the right convolution operator by a continuous kernel on the maximal compact subgroup, in the form needed to move the residual-projection and span clauses through such an averaging operator: the average is almost-everywhere additive on the truncation domain and contracts the $L^2$-norm by the $L^1$-norm of the kernel. It feeds the statement [`AutomorphicForm.paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne`](thm.html#AutomorphicForm.paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne), and rests on the invariance of `adelicGLHaar` under right translation together with the fundamental-domain property of the canonical truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact.lean

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

theorem AutomorphicForm.ae_levelTypeAverage_sub_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_kernel_maximalCompact
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    letI := adeleBorel (𝓞 K) K
    ∀ (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
      (P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
      (_hP : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
        P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ) (_hψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ψ),
    (∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)), Integrable (fun k : ↥(adelicMaximalCompact K) => κ k * φ (g * (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K)) ∧
    (∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)), P (φ - ψ) g = P φ g - P ψ g) ∧
    eLpNorm (P φ) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ ENNReal.ofReal (∫ k, ‖κ k‖ ∂(maximalCompactHaar K)) * eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
