-- Prove2me | Theorems.Thm_CurrentAFT_NumericalGaussianAccuracy_gaussian_with_numerics
-- name    : CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:55:55.288621+00:00
-- url     : https://prove2.me/theorems/d392a0e6-ad97-453f-a18d-1c6ac6e443ee
-- title:
--   Gaussian affine transport with a negligible additional numerical error
-- statement:
--   Fix an accuracy order $c\in\mathbb N$ and a negligible real-valued function $\eta:\mathbb N\to\mathbb R$, using the project's `AFT.Negligible` convention. Set $R=\mathrm{Parameters.calibrationOrder}(c)$. For all sufficiently large security parameters $\lambda$, the complete-stability threshold for $R$ is satisfied, and for every bijective layout of public roles onto body indices the calibrated weight has positive charged mass $M$ satisfying
--   $$M\ge\frac1{2q},$$
--   where $q$ is the family modulus. For that same weight, layout and positive-mass witness, the Gaussian affine-transport law satisfies
--   $$\Delta\!\left(P_{\mathrm{Gaussian\ transport}},U_{\mathrm{zero\ fiber}}\right)+\eta(\lambda)\le\lambda^{-c}.$$
--   The laws are precisely `CurrentAffineTransport.gaussianLaw` and `CurrentZeroFiber.uniformFiber`. The cutoff may depend on $c$ and $\eta$, but works simultaneously for every layout. This estimate absorbs a negligible additional numerical error into the fixed-order accuracy guarantee.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/CurrentAFT/NumericalGaussianAccuracy.lean, lines 37-86. Exact native theorem type with the complete oracle-selected proof dependency cluster. Source SHA256 48c0ba99582fa612325adb73cd4c4e9062d199492ed0ee2d2708425fa2f53333.

import Definitions.Def_InfoLossLAR_NativeBundle_12


























namespace InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates
end InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates
section



/-! # The actual Fourier budget has the manuscript's fixed-order decay -/
namespace CurrentAFT.ActualCalibrationRates
open ActualCalibrationFourier ActualCalibrationClipping
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false













set_option maxRecDepth 8192
theorem _root_.InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two (accuracyOrder : ℕ) : 2 ≤ Parameters.calibrationOrder accuracyOrder := by
  unfold Parameters.calibrationOrder
  omega
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0




end
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0

end CurrentAFT.ActualCalibrationRates
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0


end
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0

section



/-! Numerical implementation error fits the existing calibration order.
The proof retains the spare two inverse powers in the analytic estimate;
it never raises the manuscript's order `4*a+267`. -/
namespace CurrentAFT.NumericalGaussianAccuracy
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineTransport CurrentPublicAffineSample CurrentZeroFiber
  ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
  ActualCalibrationClipping ActualGaussianAccuracy
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount



set_option maxRecDepth 8192

theorem _root_.CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics (accuracyOrder : ℕ) (extra : ℕ → ℝ) (hextra : Negligible extra) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∃ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (_p2mH0 accuracyOrder) ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      ∃ hpositive : 0<publicCoreMass (proposal security)
        (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
          (_p2mH0 accuracyOrder) hsecurity layout) (publicCharge security),
        1/(2*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security)
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (_p2mH0 accuracyOrder) hsecurity layout) (publicCharge security) ∧
        (gaussianLaw security layout
          (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (_p2mH0 accuracyOrder) hsecurity layout) hpositive).totalVariation
          (uniformFiber security)+extra security  ≤  (security : ℝ)^(-(accuracyOrder : ℝ)) := by sorry
