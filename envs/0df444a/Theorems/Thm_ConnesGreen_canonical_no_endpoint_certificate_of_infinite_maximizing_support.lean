-- Prove2me | Theorems.Thm_ConnesGreen_canonical_no_endpoint_certificate_of_infinite_maximizing_support
-- name    : ConnesGreen.canonical_no_endpoint_certificate_of_infinite_maximizing_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T06:48:18.517017+00:00
-- url     : https://prove2.me/theorems/5214ece4-28b7-4213-9e6a-500464e2dd4f
-- title:
--   One infinitely supported actual maximizing profile defeats every endpoint cutoff
-- statement:
--   If the ORIGINAL sharp loss $\mu>0$ has a maximizing physical vector whose ACTUAL positive analysis is infinitely supported, meaning EVERY finite actual-zero cutoff omits a column with NONZERO inner product on that same vector, then EVERY ORIGINAL finite selected correction fails nonnegativity at EXACT accuracy $\delta=\mu$. This is a conditional obstruction using the original actual columns. Existence of such an infinitely supported maximizing profile is not asserted.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/PositiveEndpointSupport.lean, exact declaration ConnesGreen.canonical_no_endpoint_certificate_of_infinite_maximizing_support, compiling source c9aab301faeba96dcda203002677d6cf2cf396c6

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

import Theorems.Thm_ConnesGreen_canonical_endpoint_certificate_iff_pointwise_finite_support
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative ContinuousFunctionalCalculus WeilDefect.MarkerStability

theorem ConnesGreen.canonical_no_endpoint_certificate_of_infinite_maximizing_support
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S) (x : Physical t)
    (hx : x ∈ canonicalMaximizingSpace t ht S)
    (hinfinite : ∀ F : Finset CriticalZeros, ∃ ρ : CriticalZeros, ρ ∉ F ∧
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ ≠ 0) :
    ∀ F : Finset CriticalZeros,
      ¬ 0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S) := by sorry
