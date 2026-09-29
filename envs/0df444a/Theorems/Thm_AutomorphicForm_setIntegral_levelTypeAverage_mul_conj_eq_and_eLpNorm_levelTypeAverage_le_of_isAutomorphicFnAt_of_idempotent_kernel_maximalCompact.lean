-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact
-- name    : AutomorphicForm.setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/64dd7516-d360-540e-a223-3f726771ff9b
-- title:
--   Idempotent compact average is self-adjoint and contractive
-- statement:
--   Let $K$ be a number field (with decidable equality on the height one spectrum of $\mathcal O_K$), let $0<\alpha<\beta$ be reals, and let $\xi_K$ be a homomorphism from the full unit group $(\mathbb A_K)^\times$, viewed as the subgroup $\top$, to $\mathbb C^\times$. Let $\kappa$ be a continuous complex function on $\mathbf K =$ `adelicMaximalCompact K`, the subgroup of $\mathrm{GL}_2(\mathbb A_K)$ of elements whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place is a row isometry (determinant of absolute value $1$ and preservation of the sum of squared norms of the two row-combinations), assumed self-adjoint, $\kappa(k^{-1}) = \overline{\kappa(k)}$, and idempotent for convolution against the Haar measure `maximalCompactHaar K` of $\mathbf K$: $\int_{\mathbf K}\kappa(k')\kappa(k'^{-1}k)\,dk' = \kappa(k)$ for all $k$. Fix the carrier pins `productionPinsOf` with domain $\Phi_0 =$ `canonicalTruncationDomain K α β`, measurable structure and measure the Borel structure and Haar measure `adelicGLHaar (Fin 2)` on $\mathrm{GL}_2(\mathbb A_K)$, central subgroup $\top$, level subgroups $M \mapsto$ `principalLevel` $\sqcap$ `finiteAdelicGL2Subgroup` (the kernel of the archimedean projection), Hecke generators `heckeGen`, and adelic measure the additive adelic Haar measure conditioned on `adelicBox K`. Then for all $\varphi,\psi : \mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ satisfying `IsAutomorphicFnAt` for these pins and $\xi_K$: the average $P\varphi(g) = \int_{\mathbf K}\kappa(k)\varphi(gk)\,dk$ again satisfies `IsAutomorphicFnAt` for the same pins and $\xi_K$; moreover $\int_{\Phi_0} P\varphi(g)\,\overline{\psi(g)} = \int_{\Phi_0}\varphi(g)\,\overline{P\psi(g)}$ against `adelicGLHaar`, and the $L^2$-seminorm `eLpNorm` of $P\varphi$ with respect to that Haar measure restricted to $\Phi_0$ is at most that of $\varphi$.
--
--   This records the Hilbert-space properties of right convolution against a self-adjoint convolution-idempotent kernel on the maximal compact subgroup: such an average preserves the automorphy conditions packaged in the principal-level pins and acts as an orthogonal projection (self-adjoint and norm-contracting) on the $L^2$ space over the canonical truncation domain. It is used in the Paley–Wiener matching and pseudo-Eisenstein orthogonality arguments, and in the identification of the archimedean cut submodule for the residual projection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact.lean

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

theorem AutomorphicForm.setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (κ : ↥(adelicMaximalCompact K) → ℂ) (hκ : Continuous κ) (hκs : ∀ k, κ k⁻¹ = conj (κ k))
    (hκi : ∀ k : ↥(adelicMaximalCompact K), ∫ k', κ k' * κ (k'⁻¹ * k) ∂(maximalCompactHaar K) = κ k) :
    ∀ φ ψ : AdelicGL2 (𝓞 K) K → ℂ,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ → IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ψ →
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (fun g => (∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) ∧
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) * conj (ψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            φ g * conj (∫ k, κ k * ψ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ∧
        eLpNorm (fun g => (∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
