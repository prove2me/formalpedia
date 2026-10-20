-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularTorusFormCurvatureDensity
-- name    : Ehrhart.WeightedTorusBochner.integrable_angularTorusFormCurvatureDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:57.23131+00:00
-- url     : https://prove2.me/theorems/dfc7a861-0929-4a27-b3f2-7ac818919113
-- title:
--   Ehrhart.WeightedTorusBochner.integrable_angularTorusFormCurvatureDensity
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
open Ehrhart.WeightedTorusBochner
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.WeightedTorusBochner.integrable_angularTorusFormCurvatureDensity
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    Integrable (angularTorusFormCurvatureDensity a W)
      (angularWeightedTorusMeasure a) := by sorry
