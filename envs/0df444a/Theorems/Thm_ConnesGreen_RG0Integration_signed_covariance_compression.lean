-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_signed_covariance_compression
-- name    : ConnesGreen.RG0Integration.signed_covariance_compression
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:39:09.555135+00:00
-- url     : https://prove2.me/theorems/9f894a20-de6f-4c59-85c7-fc0fe961d0e9
-- title:
--   Exact original signed covariance compression under actual-source column custody
-- statement:
--   For original positive windows $t,T$ and unchanged finite actual-zero packet $S$, let $U:H_t\to H_T$ be a linear isometry satisfying $U^*\operatorname{sourceEmbed}_T(a_\rho)=\operatorname{sourceEmbed}_t(a_\rho)$ for every actual zeta-zero source. The original positive and selected-negative syntheses then satisfy $$U^*(P_TP_T^*-M_TM_T^*)U=P_tP_t^*-M_tM_t^*.$$ Their basis custody and uniqueness prove the identity. The column-compression premise is explicit; the original support-window inclusion construction supplies it in the native development.
-- source:
--   monocap-tech/weil: WeilDefect/Connes/RG0DependencyIntegration.lean, original actor and metric adapters at 4ba3a3a569d72a0d5af2ba6ea320f948030dcca5; proof and statement boundaries recovered with Lean elaborator metadata.

import Definitions.Def_ConnesGreen_RG0_original_actors
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem ConnesGreen.RG0Integration.signed_covariance_compression (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hsource : ∀ ρ : CriticalZeros,
      U.toContinuousLinearMap.adjoint (sourceEmbed T (actualGreenSource ρ)) =
        sourceEmbed t (actualGreenSource ρ)) :
    U.toContinuousLinearMap.adjoint ∘L
      (canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
        (canonicalSelectedSynthesis T hT S).adjoint) ∘L U.toContinuousLinearMap =
      canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L
        (canonicalSelectedSynthesis t ht S).adjoint := by sorry
