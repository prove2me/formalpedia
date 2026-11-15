-- Prove2me | Theorems.Thm_CurrentAFT_ActualCompletePhysical_selected_physical_explicit_order
-- name    : CurrentAFT.ActualCompletePhysical.selected_physical_explicit_order
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T21:32:14.985199+00:00
-- url     : https://prove2.me/theorems/ba94c91f-bdff-413f-9f54-e3f3fe86acf2
-- title:
--   Exact selected physical response with an explicit positive-order witness
-- statement:
--   For every security parameter, primary and body arities, order at least two, an explicitly supplied proof that the order is at least one, integer queue, tagged selection, bijective role-to-body layout, and canonical local kernel, the selected complete physical generating polynomial equals the background evaluation of the fixed-queue background multiplied by the normalized joint response plus the selected defect. The equality retains the actual finite public-permutation average and uses the original physical output mass.
-- source:
--   A version of the original public theorem selected_physical from CurrentAFT/ActualCompletePhysical.lean. The new explicitly quantified positive-order witness is redundant under the retained order-at-least-two assumption and replaces only the two implicit Omega proofs in the result type. Its complete proof and all required mathematical helpers are extracted from the original Lean syntax/kernel dependency graph. This theorem node splits the existing full Gaussian-with-numerics proof into two independently checked packages, retaining the exact original target metadata.

import Definitions.Def_InfoLossLAR_NativeBundle_12
import Mathlib
open CurrentAFT
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection ControlCoordinates
  LocalCoefficientFamily GradedControlAlgebra CycleRootExpansion ActualLayouts
  ActualRootDefectPhysical RootActualOutputPolynomial RootIndependentSelectedPhysical
  PhysicalPolynomialAverages LocalReferenceEnergy ActualFockBound ActualRootFamily
  ConditionalHistogramMean UniformTaggedOutput CompleteRaisingEvaluation ActualCycleMeanMGF
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CurrentAFT.ActualCompletePhysical.finDecEq
attribute [local instance] CurrentAFT.ActualCompletePhysical.sumDecEq
attribute [local instance] CurrentAFT.ActualCompletePhysical.vertexDecEq
attribute [local irreducible] CurrentAFT.Parameters.base CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension CurrentAFT.Parameters.legCount

theorem _root_.CurrentAFT.ActualCompletePhysical.selected_physical_explicit_order {security r s : ℕ} (order : ℕ) (horder : 2 ≤ order) (hpositive : 1 ≤ order)
    (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.TruncatedOutput.quotientMap order
      (_root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))
        (fun permutation => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.TaggedOutputFock.outputMass security r s selection layout queue permutation kernel.val))) =
      _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue *
          (_root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order hpositive kernel +
            _root_.CurrentAFT.ActualRootDefect.selectedDefect order hpositive queue selection (_root_.CurrentAFT.ActualLayouts.blockLayout layout) kernel)) := by sorry
