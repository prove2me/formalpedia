-- Prove2me | Theorems.Thm_Ehrhart_TorusClosedMollifiedRootBochner_angularWeakDolbeaultResolvent_components_mem_graph
-- name    : Ehrhart.TorusClosedMollifiedRootBochner.angularWeakDolbeaultResolvent_components_mem_graph
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/f5149642-c1d7-4268-9fdc-9e93072d6a17
-- title:
--   Ehrhart.TorusClosedMollifiedRootBochner.angularWeakDolbeaultResolvent_components_mem_graph
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
open Ehrhart.TorusClosedMollifiedRootBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open WeightedTorusBrascampLieb TorusNoncompactBochner TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff

theorem Ehrhart.TorusClosedMollifiedRootBochner.angularWeakDolbeaultResolvent_components_mem_graph
    {n : ℕ} (a : LogTorus n → ℝ)
    (g : angularWeightedScalarL2 a) :
    WithLp.toLp 2
      (angularWeakScalarResolventCLM a g,
       WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)) ∈
      angularDolbeaultGraph a := by sorry
