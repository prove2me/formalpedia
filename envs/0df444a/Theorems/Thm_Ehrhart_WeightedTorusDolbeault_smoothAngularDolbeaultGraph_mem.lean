-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusDolbeault_smoothAngularDolbeaultGraph_mem
-- name    : Ehrhart.WeightedTorusDolbeault.smoothAngularDolbeaultGraph_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:57.23131+00:00
-- url     : https://prove2.me/theorems/74d891c5-9360-40dd-a926-9f56dfb4001e
-- title:
--   Ehrhart.WeightedTorusDolbeault.smoothAngularDolbeaultGraph_mem
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
open Ehrhart.WeightedTorusDolbeault
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.WeightedTorusDolbeault.smoothAngularDolbeaultGraph_mem {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hcont : ContDiff ℝ 3 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    WithLp.toLp 2
      (angularScalarL2OfRepresentative a F hF,
       angularBarPartialL2OfRepresentative a F hD) ∈
        angularDolbeaultGraph a := by sorry
