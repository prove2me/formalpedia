-- Prove2me | Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact
-- name    : AutomorphicForm.isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/3334cdd1-b988-5157-992c-8764b0b0922c
-- title:
--   Right K-translates and kernel averages of automorphic L² members
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta\in\mathbb R$ with $0<\alpha$ and $\alpha<\beta$, and let $\xi_K$ be a monoid homomorphism from the full subgroup $\top$ of $(\mathbb A_K)^\times$ to $\mathbb C^\times$. Write $\Phi_0=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) and let the data be the pins `productionPinsOf` attached to $\Phi_0$, to the level subgroups $N\mapsto$ `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, to the Hecke elements `heckeGen (𝓞 K) K v` and to the box `adelicBox K`; these pins carry the Borel structure `glBorel` on $GL_2(\mathbb A_K)$, the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`, the domain $\Phi_0$, the central subgroup $\top$ and the conditioned additive Haar measure on `adelicBox K`. The conclusion asserts, for every continuous $\kappa:\mathbf K\to\mathbb C$ on the maximal compact $\mathbf K=$ `adelicMaximalCompact K` (those $k$ whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place satisfies `IsRowIsometry`, i.e. has determinant of norm $1$ and preserves $\|x\|^2+\|y\|^2$ on row vectors), and for all $\varphi,\psi:GL_2(\mathbb A_K)\to\mathbb C$ satisfying `IsAutomorphicFnAt` for these pins and $\xi_K$: (a) for every $k\in\mathbf K$ the right translate $g\mapsto\varphi(gk)$ again satisfies `IsAutomorphicFnAt` for the same pins and $\xi_K$, and has the same $L^2$ norm with respect to `adelicGLHaar` restricted to $\Phi_0$ as $\varphi$; (b) for almost every $g$ with respect to that restricted measure, $k\mapsto\kappa(k)\varphi(gk)$ is integrable for `maximalCompactHaar K`, the Haar measure of $\mathbf K$ normalised at $\top$; (c) for almost every such $g$, $\int_{\mathbf K}\kappa(k)(\varphi-\psi)(gk)\,dk=\int_{\mathbf K}\kappa(k)\varphi(gk)\,dk-\int_{\mathbf K}\kappa(k)\psi(gk)\,dk$; (d) $g\mapsto\int_{\mathbf K}\kappa(k)\varphi(gk)\,dk$ again satisfies `IsAutomorphicFnAt` for the same pins and $\xi_K$, and its $L^2$ norm over $\Phi_0$ is at most $\bigl(\int_{\mathbf K}\|\kappa(k)\|\,dk\bigr)$ times that of $\varphi$.
--
--   This is the statement that right translation by the maximal compact subgroup acts isometrically on the automorphic members of $L^2$ over the truncation domain, and that convolution against a continuous kernel on $\mathbf K$ is a linear operator on this space bounded by the $L^1$ norm of the kernel. It is used in the construction of the level-type averaging projector and in the analysis of idempotent kernels on the maximal compact.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact.lean

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

theorem AutomorphicForm.isAutomorphicFnAt_comp_mul_and_eLpNorm_eq_and_eLpNorm_levelTypeAverage_le_of_kernel_maximalCompact
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) :
    ∀ (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
      (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ)
      (_hψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ψ),
    (∀ k : ↥(adelicMaximalCompact K),
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (fun g => φ (g * (k : AdelicGL2 (𝓞 K) K))) ∧
      eLpNorm (fun g => φ (g * (k : AdelicGL2 (𝓞 K) K))) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) = eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) ∧
    (∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)),
      Integrable (fun k : ↥(adelicMaximalCompact K) => κ k * φ (g * (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K)) ∧
    (∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)),
      (∫ k, κ k * (φ - ψ) (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = (∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) - (∫ k, κ k * ψ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) ∧
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (fun g => (∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) ∧
    eLpNorm (fun g => (∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
      ENNReal.ofReal (∫ k, ‖κ k‖ ∂(maximalCompactHaar K)) * eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
