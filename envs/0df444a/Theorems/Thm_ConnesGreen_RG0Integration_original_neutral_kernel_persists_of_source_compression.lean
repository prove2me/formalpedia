-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_original_neutral_kernel_persists_of_source_compression
-- name    : ConnesGreen.RG0Integration.original_neutral_kernel_persists_of_source_compression
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:47:13.082985+00:00
-- url     : https://prove2.me/theorems/39adcaab-9aed-4dd8-b38b-8dff36b3d1cb
-- title:
--   Original neutral-kernel persistence under source compression and larger-window positivity
-- statement:
--   Under the original actual-source compression premise of the preceding covariance identity, suppose the larger-window original signed covariance $D_T=P_TP_T^*-M_TM_T^*$ is nonnegative. Then, for every vector in the original smaller completed physical carrier, $$D_tx=0\iff D_TUx=0.$$ The accepted nonnegative-compression kernel theorem is applied to the exact original signed covariance. Larger-window positivity is an explicit premise; the theorem does not assert unconditional neutral attainment or persistence at the unresolved critical endpoint.
-- source:
--   monocap-tech/weil: WeilDefect/Connes/RG0DependencyIntegration.lean, original actor and metric adapters at 4ba3a3a569d72a0d5af2ba6ea320f948030dcca5; proof and statement boundaries recovered with Lean elaborator metadata.

import Theorems.Thm_ConnesGreen_RG0Integration_signed_covariance_compression
import Theorems.Thm_WeilDefect_MarkerStability_nonnegative_compression_kernel_iff
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem ConnesGreen.RG0Integration.original_neutral_kernel_persists_of_source_compression (t T : ℝ)
    (ht : 0 < t) (hT : 0 < T) (S : Finset CriticalZeros)
    (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hsource : ∀ ρ : CriticalZeros,
      U.toContinuousLinearMap.adjoint (sourceEmbed T (actualGreenSource ρ)) =
        sourceEmbed t (actualGreenSource ρ))
    (hpos : 0 ≤ canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
      (canonicalSelectedSynthesis T hT S).adjoint) (x : Physical t) :
    (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L
      (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔
    (canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
      (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0 := by sorry
