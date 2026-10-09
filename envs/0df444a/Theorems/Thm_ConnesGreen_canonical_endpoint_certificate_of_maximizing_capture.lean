-- Prove2me | Theorems.Thm_ConnesGreen_canonical_endpoint_certificate_of_maximizing_capture
-- name    : ConnesGreen.canonical_endpoint_certificate_of_maximizing_capture
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T06:35:17.74999+00:00
-- url     : https://prove2.me/theorems/2f891493-7137-43e0-865a-9bd1e94f3d52
-- title:
--   Exact maximizing-space capture constructs original endpoint certificates
-- statement:
--   Suppose the ORIGINAL sharp loss $\mu>0$ and one finite ACTUAL positive cutoff $F_0$ annihilates EVERY omitted original positive column on EVERY vector of the ORIGINAL maximizing eigenspace. Then for EVERY complete-tail accuracy $\varepsilon>0$ there exists a finite cutoff $F\supseteq S\cup F_0$, closed under actual-zero reflection, with complete omitted positive column square-norm tail below $\varepsilon$ and the ORIGINAL finite selected correction nonnegative at EXACT accuracy $\delta=\mu$. The selected packet, physical carrier, full positive actor and correction are unchanged; no endpoint certificate is assumed.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/PositiveEndpointSupport.lean, exact declaration ConnesGreen.canonical_endpoint_certificate_of_maximizing_capture, compiling source c9aab301faeba96dcda203002677d6cf2cf396c6

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

import Theorems.Thm_ConnesGreen_canonicalPositiveCovariance_compact
import Theorems.Thm_ConnesGreen_canonical_positive_threshold_orthogonal_gap
import Theorems.Thm_WeilDefect_MarkerStability_regularized_covariance_le_iff_selected_correction
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative ContinuousFunctionalCalculus WeilDefect.MarkerStability

theorem ConnesGreen.canonical_endpoint_certificate_of_maximizing_capture
    (t : ℝ) (ht : 0 < t) (S F₀ : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S)
    (hcapture : ∀ x : Physical t, x ∈ canonicalMaximizingSpace t ht S →
      ∀ ρ : CriticalZeros, ρ ∉ F₀ →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧ F₀ ⊆ F ∧
      (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) < ε ∧
      0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S) := by sorry
