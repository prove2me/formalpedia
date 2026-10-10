-- Prove2me | Theorems.Thm_ConnesGreen_canonical_endpoint_finite_sampling_obstruction
-- name    : ConnesGreen.canonical_endpoint_finite_sampling_obstruction
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T13:23:33.450886+00:00
-- url     : https://prove2.me/theorems/148421a1-0787-41be-bb7c-c754bf4808f5
-- title:
--   Positive endpoint certificates force a finite actor eigen-equation with actual sampling constraints
-- statement:
--   At positive original sharp loss $\mu>0$, nonnegativity of an ORIGINAL finite selected correction at exact accuracy $\delta=\mu$, with fixed actual cutoff $F$, forces a NONZERO original physical vector satisfying BOTH $$\mu x=\sum_{\rho\in S}\langle n_\rho,x\rangle n_\rho-\sum_{\rho\in F}\langle p_\rho,x\rangle p_\rho$$ and $$\langle p_\rho,x\rangle=0\quad(\rho\notin F).$$ Here $n_\rho,p_\rho$ are the unchanged actual negative and positive reflection-pair columns, with original multiplicities. The infinitely many omitted sampling equations remain part of the conclusion; a finite matrix eigen-equation alone is not claimed sufficient for the endpoint certificate.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/EndpointFiniteReconstruction.lean, exact declaration ConnesGreen.canonical_endpoint_finite_sampling_obstruction, compiling source 5f573c18985ee59bff27315944cd5bb75a488e01

import Definitions.Def_ConnesGreen_positive_endpoint_support

import Theorems.Thm_ConnesGreen_canonical_positive_threshold_attained
import Theorems.Thm_ConnesGreen_canonical_finite_certificate_neutral_tail_zero
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative

theorem ConnesGreen.canonical_endpoint_finite_sampling_obstruction
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S)) :
    ∃ x : Physical t, x ≠ 0 ∧
      (canonicalCertificateThreshold t ht S : ℂ) • x =
        (∑ ρ ∈ S, ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
          negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) -
        (∑ ρ ∈ F, ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
          positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) := by sorry
