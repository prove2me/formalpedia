-- Prove2me | Theorems.Thm_Ehrhart_TorusStrongCoverMollification_normalizedCoverMollification_continuous_compact_L2_tendsto
-- name    : Ehrhart.TorusStrongCoverMollification.normalizedCoverMollification_continuous_compact_L2_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/5f011e26-5164-45b1-9961-5bd22c431a12
-- title:
--   Ehrhart.TorusStrongCoverMollification.normalizedCoverMollification_continuous_compact_L2_tendsto
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
open Ehrhart.TorusStrongCoverMollification
open Set Function Filter MeasureTheory
open TorusCharacters MatrixTorusBochnerCoreApproximation TorusWeakDolbeaultMollification
open TorusMollificationLocalL2Bounds TorusCompactTestGreen
open scoped ENNReal Topology ContDiff Convolution

theorem Ehrhart.TorusStrongCoverMollification.normalizedCoverMollification_continuous_compact_L2_tendsto
    {n : ℕ} {h : LogSpace n → ℂ}
    (hc : Continuous h) (hs : HasCompactSupport h) :
    Tendsto
      (fun k : ℕ =>
        (normalizedCoverMollification_memLp
          (hc.memLp_of_hasCompactSupport hs) k).toLp
            (normalizedCoverMollification h k))
      atTop
      (nhds
        ((hc.memLp_of_hasCompactSupport hs).toLp h)) := by sorry
