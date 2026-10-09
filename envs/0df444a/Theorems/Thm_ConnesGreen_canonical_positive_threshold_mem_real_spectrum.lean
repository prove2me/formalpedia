-- Prove2me | Theorems.Thm_ConnesGreen_canonical_positive_threshold_mem_real_spectrum
-- name    : ConnesGreen.canonical_positive_threshold_mem_real_spectrum
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T05:53:04.565837+00:00
-- url     : https://prove2.me/theorems/5b73162f-08a2-4c5c-9d04-0f96185d5f6f
-- title:
--   A positive original sharp loss lies in the real spectrum
-- statement:
--   Fix the original completed physical carrier and one finite actual-zero selected packet. If the original sharp loss $\mu$ is positive, then $\mu$ belongs to the REAL spectrum of the original self-adjoint loss covariance $A=N_SN_S^*-PP^*$. This proves spectral membership without assuming attainment, RH or positivity.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/ThresholdSpectrum.lean, exact declaration ConnesGreen.canonical_positive_threshold_mem_real_spectrum, compiling source ab20377e04b8056e6db154b7054f60e0ce0a8f00

import Definitions.Def_ConnesGreen_selected_loss_covariance
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

import Theorems.Thm_ConnesGreen_canonical_selected_form_ge_overlap_shift
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative
open ContinuousFunctionalCalculus

theorem ConnesGreen.canonical_positive_threshold_mem_real_spectrum (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (hμ : 0 < canonicalCertificateThreshold t ht S) :
    canonicalCertificateThreshold t ht S ∈ spectrum ℝ (canonicalLossCovariance t ht S) := by sorry
