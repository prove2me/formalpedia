-- Prove2me | Theorems.Thm_ConnesGreen_canonical_positive_threshold_orthogonal_gap
-- name    : ConnesGreen.canonical_positive_threshold_orthogonal_gap
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T06:29:26.882476+00:00
-- url     : https://prove2.me/theorems/64fa9cc8-c932-462c-a059-a67a66c37aa6
-- title:
--   A positive sharp loss has a derived orthogonal spectral gap
-- statement:
--   Fix the ORIGINAL positive support window and finite actual-zero selected packet. If its sharp loss $\mu$ is positive, the ORIGINAL sharp shifted margin has a POSITIVE uniform gap on the orthogonal complement of the actual maximizing eigenspace $E=\ker(A-\mu I)$, where $A=N_SN_S^*-PP^*$: $$\exists c>0\quad\forall x\in E^\perp,\quad c\|x\|^2\le\|P^*x\|^2-\|N_S^*x\|^2+\mu\|x\|^2.$$ The spectral gap is derived from original compactness and the sharp bound, not postulated. Actual-zero multiplicities and the complete positive actor remain unchanged.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/PositiveEndpointSupport.lean, exact declaration ConnesGreen.canonical_positive_threshold_orthogonal_gap, compiling source c9aab301faeba96dcda203002677d6cf2cf396c6

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

import Theorems.Thm_ConnesGreen_canonicalPositiveCovariance_compact
import Theorems.Thm_ConnesGreen_canonical_selected_form_ge_overlap_shift
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative ContinuousFunctionalCalculus WeilDefect.MarkerStability

theorem ConnesGreen.canonical_positive_threshold_orthogonal_gap (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (hμ : 0 < canonicalCertificateThreshold t ht S) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Physical t,
      x ∈ (canonicalMaximizingSpace t ht S)ᗮ →
      c * ‖x‖ ^ 2 ≤ canonicalSharpMargin t ht S x := by sorry
