-- Prove2me | Theorems.Thm_CurrentAFT_ActualCalibratedPublic_positive_eventually
-- name    : CurrentAFT.ActualCalibratedPublic.positive_eventually
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T16:59:35.050316+00:00
-- url     : https://prove2.me/theorems/5505b921-f096-400e-98eb-a4abfee39bde
-- title:
--   Eventual charge-mass and output bounds for the positive calibrated public law
-- statement:
--   For every accuracy order $c\in\mathbb N$, set $R=\mathrm{Parameters.calibrationOrder}(c)$. There exists a security cutoff such that the following holds for every larger $\lambda$, every witness that $\lambda$ exceeds the complete-stability threshold for $R$, and every bijective layout of public roles onto body indices. Assume the calibrated public weight satisfies `ActualCalibratedPublic.Calibrated` for these parameters and layout.
--   Let $q$ be the family modulus and let $M$ be `publicCoreMass` of the public proposal, this weight, and the public charge event. Then $M>0$ and
--   $$M\ge\frac1{2q}.$$
--   The corresponding `positivePublicCoreLaw`, followed by the actual public-experiment channel for the same layout, obeys
--   $$\Delta\!\left(P_{\mathrm{out}},U_{\mathrm{zero\,sum}}\right)\le 2q\left(E_{\mathrm{Fourier}}(\lambda,R)+E_{\mathrm{clip}}(\lambda,R,\mathrm{layout})\right).$$
--   Here $U_{\mathrm{zero\,sum}}$ is `FiniteZeroSum.uniformLaw`, $E_{\mathrm{Fourier}}$ is `ActualCalibrationRates.fourierError`, and $E_{\mathrm{clip}}$ is `ActualCalibrationClipping.loss` with the associated block layout and threshold witness. Thus the charged positive law has sufficient normalizing mass and controlled output total variation.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/CurrentAFT/ActualCalibratedPublic.lean, lines 76-113. Exact native theorem type with the complete oracle-selected proof dependency cluster. Source SHA256 c859038a3e101d61c21c04608430066a757577cae231d4b02aba1482dfcd12e8.

import Definitions.Def_InfoLossLAR_NativeBundle_08











namespace InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates
end InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates
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
theorem _root_.InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two (accuracyOrder : ℕ) : 2 ≤ Parameters.calibrationOrder accuracyOrder := by
  unfold Parameters.calibrationOrder
  omega
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0




end
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0

end CurrentAFT.ActualCalibrationRates
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0


end
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.ActualCalibratedPublic.positive_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0

section




/-! # Positive publicly charged sampling with the actual calibrated weight -/
namespace CurrentAFT.ActualCalibratedPublic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge ActualPublicExperiment
  ActualCalibrationFourier ActualCalibrationRates ActualCalibrationClipping ActualCompleteStability
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

attribute [local instance] _root_.CurrentAFT.ActualCalibratedPublic.endpointNonempty














set_option maxRecDepth 8192

theorem _root_.CurrentAFT.ActualCalibratedPublic.positive_eventually (accuracyOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (_p2mH0 accuracyOrder) ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security,
      Calibrated security (Parameters.calibrationOrder accuracyOrder)
        (_p2mH0 accuracyOrder) hsecurity layout →
      ∃ hpositive : 0 < publicCoreMass (proposal security)
          (weight security (Parameters.calibrationOrder accuracyOrder)
            (_p2mH0 accuracyOrder) hsecurity layout) (publicCharge security),
        1 / (2 * (Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security)
          (weight security (Parameters.calibrationOrder accuracyOrder)
            (_p2mH0 accuracyOrder) hsecurity layout) (publicCharge security) ∧
        ((positivePublicCoreLaw (proposal security)
            (weight security (Parameters.calibrationOrder accuracyOrder)
              (_p2mH0 accuracyOrder) hsecurity layout) (publicCharge security) hpositive).mix
          (channel security layout)).totalVariation
            (FiniteZeroSum.uniformLaw (Index := Fin (Parameters.dimension security)) (Parameters.modulus security)) ≤
              2 * (Parameters.modulus security : ℝ) *
                (fourierError security (Parameters.calibrationOrder accuracyOrder) +
                  loss security (Parameters.calibrationOrder accuracyOrder)
                    (_p2mH0 accuracyOrder) hsecurity (ActualLayouts.blockLayout layout)) := by sorry
