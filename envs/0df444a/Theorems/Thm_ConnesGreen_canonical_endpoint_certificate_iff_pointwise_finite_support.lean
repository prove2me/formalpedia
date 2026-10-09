-- Prove2me | Theorems.Thm_ConnesGreen_canonical_endpoint_certificate_iff_pointwise_finite_support
-- name    : ConnesGreen.canonical_endpoint_certificate_iff_pointwise_finite_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T06:40:51.183646+00:00
-- url     : https://prove2.me/theorems/4e9ded85-9925-49c2-b3b1-22483cc63158
-- title:
--   Positive endpoint certificates exactly mean finite analysis support of every maximizer
-- statement:
--   For a POSITIVE original sharp loss $\mu$, existence of an ORIGINAL finite selected certificate at EXACT $\delta=\mu$ is equivalent to the following localized condition: EVERY vector in the ORIGINAL maximizing eigenspace has FINITE support in its ACTUAL positive analysis, meaning that all its original positive-column inner products vanish outside some finite actual-zero cutoff. The cutoff MAY initially depend on the vector. Finite dimensionality and compactness are proved from the original development, so no common cutoff or spectral-gap hypothesis is left implicit. This concerns a positive endpoint, not the arithmetic zero-loss condition required for RH.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/PositiveEndpointSupport.lean, exact declaration ConnesGreen.canonical_endpoint_certificate_iff_pointwise_finite_support, compiling source c9aab301faeba96dcda203002677d6cf2cf396c6

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

import Theorems.Thm_ConnesGreen_canonicalPositiveCovariance_compact
import Theorems.Thm_ConnesGreen_canonical_endpoint_certificate_of_maximizing_capture
import Theorems.Thm_ConnesGreen_canonical_finite_certificate_neutral_tail_zero
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative ContinuousFunctionalCalculus WeilDefect.MarkerStability

theorem ConnesGreen.canonical_endpoint_certificate_iff_pointwise_finite_support
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S) :
    (∃ F : Finset CriticalZeros,
      0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S)) ↔
    (∀ x : Physical t, x ∈ canonicalMaximizingSpace t ht S →
      ∃ F : Finset CriticalZeros, ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) := by sorry
