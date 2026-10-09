-- Prove2me | Theorems.Thm_ConnesGreen_canonical_positive_threshold_attained
-- name    : ConnesGreen.canonical_positive_threshold_attained
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T06:01:15.620648+00:00
-- url     : https://prove2.me/theorems/5b0c86e3-4107-4ec1-937e-5e1e9252c6b2
-- title:
--   A positive original sharp loss is attained by a physical eigenvector
-- statement:
--   Whenever the sharp selected loss $\mu$ is positive, there exists a NONZERO vector $x$ in the ORIGINAL completed physical carrier such that $$ (N_SN_S^*-PP^*)x=\mu x,\qquad \|P^*x\|^2-\|N_S^*x\|^2+\mu\|x\|^2=0.$$ The full actual positive actor and unchanged finite actual-zero selected packet are retained. This does not assert smooth admissible-test attainment or zero-threshold attainment.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/ThresholdSpectrum.lean, exact declaration ConnesGreen.canonical_positive_threshold_attained, compiling source ab20377e04b8056e6db154b7054f60e0ce0a8f00

import Definitions.Def_ConnesGreen_selected_loss_covariance
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

import Theorems.Thm_ConnesGreen_canonicalPositiveCovariance_compact
import Theorems.Thm_ConnesGreen_canonical_positive_threshold_mem_real_spectrum
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative
open ContinuousFunctionalCalculus

theorem ConnesGreen.canonical_positive_threshold_attained (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (hμ : 0 < canonicalCertificateThreshold t ht S) :
    ∃ x : Physical t, x ≠ 0 ∧
      canonicalLossCovariance t ht S x = (canonicalCertificateThreshold t ht S : ℂ) • x ∧
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
        ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 +
          canonicalCertificateThreshold t ht S * ‖x‖ ^ 2 = 0 := by sorry
