-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularPhysicalWeakResolventRootCutoff_sq_le_adjoint_matrix
-- name    : Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularPhysicalWeakResolventRootCutoff_sq_le_adjoint_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:06.698159+00:00
-- url     : https://prove2.me/theorems/53c06533-0255-48fe-8a72-8841096742fe
-- title:
--   Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularPhysicalWeakResolventRootCutoff_sq_le_adjoint_matrix
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | EhrhartVolumeInequality | external Lean 4.33.1 validation; bundle SHA256 7150ea60aef8441515028279454832b05d0f964f3966505d147b2c1d8afe9763

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open JetEnvelopeRightDerivative EqualitySaturatingKillingPaths ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerCoreDensity
open MatrixTorusBochnerCoreApproximation MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusWeightedAdjointMollification TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open TorusWeakRadialExteriorEnergy TorusWeakRadialBochnerUpperBound
open TorusWeakRadialExteriorMollification TorusClosedMollifiedRootBochner
open TorusStrongWeightedCutoffAdjoint TorusWeakResolventRootBochner
open RadialPhysicalResolventRootCutoffUniformExtraction TorusHomogeneousSmoothRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff

theorem Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularPhysicalWeakResolventRootCutoff_sq_le_adjoint_matrix
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (g : angularWeightedScalarL2 a)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B)
    (m : ℕ) :
    let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
      ha3.of_le (by norm_num)
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    let d : angularWeightedScalarL2 a :=
      g - angularWeakScalarResolventCLM a g
    ‖angularPhysicalResolventRootCutoffL2
        ha2 hH W m‖ ^ 2 ≤
      ‖angularWeakSourceCutoffAdjointDefectL2 d W hB m‖ ^ 2 +
        2 * ‖(angularWeakSourceCutoffDerivativeCommutator_memLp
          W hB m).toLp
            (angularWeakSourceCutoffDerivativeCommutator W m)‖ ^ 2 := by sorry
