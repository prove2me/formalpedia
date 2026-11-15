-- Prove2me | Theorems.Thm_CurrentAFT_PublicAffinePipeline_accuracy_eventually
-- name    : CurrentAFT.PublicAffinePipeline.accuracy_eventually
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T21:55:30.78017+00:00
-- url     : https://prove2.me/theorems/83cea2e1-b705-46a9-88ca-c9e8866d3758
-- title:
--   Eventual Gaussian accuracy of the executed public affine pipeline
-- statement:
--   Fix $c\in\mathbb N$ and set $R=\mathrm{Parameters.calibrationOrder}(c)$. For each security parameter $\lambda$, let a producer map the stored layout to a counted coefficient table of order $R$. Let $\eta:\mathbb N\to\mathbb R$ be nonnegative and negligible. Assume that, for all sufficiently large $\lambda$, uniformly over every complete-stability threshold witness, stored layout and public core, the binary rejection weight computed from the produced table differs from the corresponding exact calibrated public weight by at most $\eta(\lambda)$.
--   Then there exists a cutoff $\lambda_0$ such that for all $\lambda\ge\lambda_0$,
--   $$\Delta\!\left(\operatorname{fairGaussian}(\lambda,R,\operatorname{producer}(\lambda)),\operatorname{uniformFiber}(\lambda)\right)\le\lambda^{-c}.$$
--   Here `fairGaussian` is the actual fair-bit public affine pipeline applied to the family Gaussian source, and `uniformFiber` is the uniform zero-fiber law. The hypothesis controls the produced weight table pointwise; the conclusion concerns the full resulting output distribution, including the pipeline's public sampling and numerical stages.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/CurrentAFT/PublicAffinePipelineAccuracy.lean, lines 19-64. Exact native theorem type with the complete oracle-selected proof dependency cluster. Source SHA256 634924908628c73c8c15801434ed1129fac6be28ec21c36428513099f81e9c3d.

import Definitions.Def_InfoLossLAR_NativeBundle_12



























namespace InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates
end InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates
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
theorem _root_.InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two (accuracyOrder : ℕ) : 2 ≤ Parameters.calibrationOrder accuracyOrder := by
  unfold Parameters.calibrationOrder
  omega
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0




end
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0

end CurrentAFT.ActualCalibrationRates
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0


end
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → CurrentAFT.ActualCalibrationRates.calibrationOrder_at_least_two
open _root_.InfoLossLARNativeProofHelpers.CurrentAFT.PublicAffinePipeline.accuracy_eventually.h2573c5b83a2a34d9.CurrentAFT.ActualCalibrationRates renaming calibrationOrder_at_least_two → _p2mH0


namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.ActualCalibratedPublic
end CurrentAFT.ActualCalibratedPublic
namespace CurrentAFT.ActualCalibratedPublic.weight
end CurrentAFT.ActualCalibratedPublic.weight
namespace CurrentAFT.CurrentAffineTransport
end CurrentAFT.CurrentAffineTransport
namespace CurrentAFT.CurrentAffineTransport.gaussianLaw
end CurrentAFT.CurrentAffineTransport.gaussianLaw
namespace CurrentAFT.NumericalGaussianAccuracy
end CurrentAFT.NumericalGaussianAccuracy
section



/-! Closing the actual public sampling and emission stages from a certified
calibration-table producer. Only the producer's weight approximation remains
an input to this composition lemma. -/
namespace CurrentAFT.PublicAffinePipeline
open AFT ActualPublicCharge ActualCompleteStability ActualGaussianAccuracy ActualCalibrationRates
open Filter
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current

set_option maxRecDepth 8192

theorem _root_.CurrentAFT.PublicAffinePipeline.accuracy_eventually (accuracyOrder : ℕ)
    (producer : ∀ security, Producer security (Parameters.calibrationOrder accuracyOrder))
    (weightError : ℕ → ℝ) (hnonneg : ∀ security, 0 ≤ weightError security) (hnegligible : Negligible weightError)
    (hweight : ∀ᶠ security : ℕ in atTop,
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (_p2mH0 accuracyOrder) ≤ security,
      ∀ (layout : CurrentLayoutDraw.Cache security) (core : Core security),
        |(BinaryPublicRejection.coreWeight security security (Parameters.calibrationOrder accuracyOrder)
          (producer security layout).value core : ℝ)-
          ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (_p2mH0 accuracyOrder) hsecurity layout.layout core| ≤ weightError security) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      (fairGaussian security (Parameters.calibrationOrder accuracyOrder) (producer security)).totalVariation
        (CurrentZeroFiber.uniformFiber security) ≤ (security : ℝ)^(-(accuracyOrder : ℝ)) := by sorry
