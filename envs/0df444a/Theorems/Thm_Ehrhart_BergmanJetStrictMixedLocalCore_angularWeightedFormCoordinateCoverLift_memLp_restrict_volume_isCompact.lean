-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetStrictMixedLocalCore_angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
-- name    : Ehrhart.BergmanJetStrictMixedLocalCore.angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/441f8a0e-32d2-4af1-aa1c-f7c8a5a18bd0
-- title:
--   Ehrhart.BergmanJetStrictMixedLocalCore.angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
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
open Ehrhart.BergmanJetStrictMixedLocalCore
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusVectorClosedGraphWeakBridge WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology

theorem Ehrhart.BergmanJetStrictMixedLocalCore.angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (W : angularWeightedFormL2 a) (i : Fin n)
    {S : Set (LogSpace n)} (hS : IsCompact S) :
    MemLp
      (complexTorusCoverLift
        (fun q : LogTorus n =>
          (W q : EuclideanSpace ℂ (Fin n)) i))
      2 ((volume : Measure (LogSpace n)).restrict S) := by sorry
