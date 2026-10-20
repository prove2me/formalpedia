-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauSlopeBridge_upperSemicontinuous_of_complexTorusCover
-- name    : Ehrhart.BergmanJetPortmanteauSlopeBridge.upperSemicontinuous_of_complexTorusCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:06.698159+00:00
-- url     : https://prove2.me/theorems/bc57205e-1f1e-4197-b7ca-bf4e117ae9f9
-- title:
--   Ehrhart.BergmanJetPortmanteauSlopeBridge.upperSemicontinuous_of_complexTorusCover
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
open Ehrhart.BergmanJetPortmanteauSlopeBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetPortmanteauSlopeBridge.upperSemicontinuous_of_complexTorusCover
    {n : ℕ} (f : LogTorus n → ℝ)
    (hf : UpperSemicontinuous
      (fun z : LogSpace n =>
        f (complexTorusCoverProjection n z))) :
    UpperSemicontinuous f := by sorry
