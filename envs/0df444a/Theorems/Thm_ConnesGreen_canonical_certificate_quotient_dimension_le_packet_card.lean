-- Prove2me | Theorems.Thm_ConnesGreen_canonical_certificate_quotient_dimension_le_packet_card
-- name    : ConnesGreen.canonical_certificate_quotient_dimension_le_packet_card
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T20:08:29.39204+00:00
-- url     : https://prove2.me/theorems/22aa6087-e787-4671-8685-45471dc3f469
-- title:
--   Original positive-error certificate quotient dimension is bounded by selected packet size
-- statement:
--   For positive original physical window and strictly positive error $\delta$, the SAME original integral certificate/Gram kernels satisfy $$\dim\ker K_\delta-\dim\ker H\le |S|.$$ Here $S$ is the ORIGINAL selected negative packet and $F$ the ORIGINAL cutoff. The bound is independent of $|F|$. It is obtained from PROVED selected-negative analysis injectivity modulo the ORIGINAL Gram kernel, not from an assumed arithmetic sampling rank. No zero-error assertion or RH is made.
-- source:
--   monocap-tech/weil, compiling source c3e7b782afd23ef5076a93915265a6584646b5e7, exact declaration ConnesGreen.canonical_certificate_quotient_dimension_le_packet_card

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_WeilDefect_MarkerStability_submodule_dimension_difference_le_analysis_card
import Theorems.Thm_ConnesGreen_canonical_gram_null_sampling_custody
import Theorems.Thm_ConnesGreen_canonical_negative_coordinates_detect_gram_null
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_certificate_quotient_dimension_le_packet_card
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ) :
    Module.finrank ℂ (LinearMap.ker (canonicalFiniteIntegralCertificate t S F δ).mulVecLin) -
      Module.finrank ℂ (LinearMap.ker (canonicalFiniteColumnKernel t S F).mulVecLin) ≤ S.card := by sorry
