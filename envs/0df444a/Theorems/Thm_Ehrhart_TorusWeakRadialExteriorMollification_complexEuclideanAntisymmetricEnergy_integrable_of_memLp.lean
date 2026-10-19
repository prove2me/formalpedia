-- Prove2me | Theorems.Thm_Ehrhart_TorusWeakRadialExteriorMollification_complexEuclideanAntisymmetricEnergy_integrable_of_memLp
-- name    : Ehrhart.TorusWeakRadialExteriorMollification.complexEuclideanAntisymmetricEnergy_integrable_of_memLp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/0c396fbb-f430-4e79-ab76-1e883c22133c
-- title:
--   Ehrhart.TorusWeakRadialExteriorMollification.complexEuclideanAntisymmetricEnergy_integrable_of_memLp
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
open Ehrhart.TorusWeakRadialExteriorMollification
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedPoincare WeightedBrascampLieb
open WeightedResolventConstantCore EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreApproximation MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault
open TorusMollifiedBochner TorusNoncompactBochner TorusWeakRadialCutoffCommutator
open TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff

theorem Ehrhart.TorusWeakRadialExteriorMollification.complexEuclideanAntisymmetricEnergy_integrable_of_memLp
    {n : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {M : X → EuclideanSpace ℂ (Fin n × Fin n)}
    (hM : MemLp M 2 μ) :
    Integrable
      (fun x : X => complexEuclideanAntisymmetricEnergy (M x)) μ := by sorry
