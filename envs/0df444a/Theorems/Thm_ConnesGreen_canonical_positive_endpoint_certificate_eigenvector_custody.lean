-- Prove2me | Theorems.Thm_ConnesGreen_canonical_positive_endpoint_certificate_eigenvector_custody
-- name    : ConnesGreen.canonical_positive_endpoint_certificate_eigenvector_custody
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T06:05:50.095969+00:00
-- url     : https://prove2.me/theorems/ade34847-8808-4fa9-a701-e9df19b3e892
-- title:
--   An endpoint certificate must capture an attained physical maximizing direction
-- statement:
--   If the original sharp selected loss $\mu$ is positive and the ORIGINAL finite selected correction is nonnegative at EXACT accuracy $\delta=\mu$, then there exists a NONZERO original physical eigenvector $x$ of $N_SN_S^*-PP^*$ at $\mu$ which is shifted neutral and satisfies $$\langle p_\rho,x\rangle=0\quad\text{for EVERY actual positive column with }\rho\notin F.$$ No packet-containment or reflection-closure premise is needed. This is a necessary endpoint constraint, not existence of endpoint certificates.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/ThresholdSpectrum.lean, exact declaration ConnesGreen.canonical_positive_endpoint_certificate_eigenvector_custody, compiling source ab20377e04b8056e6db154b7054f60e0ce0a8f00

import Definitions.Def_ConnesGreen_selected_loss_covariance
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

import Theorems.Thm_ConnesGreen_canonical_positive_threshold_attained
import Theorems.Thm_ConnesGreen_canonical_finite_certificate_neutral_tail_zero
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative
open ContinuousFunctionalCalculus

theorem ConnesGreen.canonical_positive_endpoint_certificate_eigenvector_custody
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F
      (canonicalCertificateThreshold t ht S)) :
    ∃ x : Physical t, x ≠ 0 ∧
      canonicalLossCovariance t ht S x = (canonicalCertificateThreshold t ht S : ℂ) • x ∧
      (‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
        ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 +
          canonicalCertificateThreshold t ht S * ‖x‖ ^ 2 = 0) ∧
      ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0 := by sorry
