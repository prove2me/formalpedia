-- Prove2me | Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceTorusCoverPoint_mem_shrinkingBall_of_mem_box
-- name    : Ehrhart.JetEnvelopeLocalGrowth.sourceTorusCoverPoint_mem_shrinkingBall_of_mem_box
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/a0aa9cdb-4cfd-4ef9-b574-570fcc239d95
-- title:
--   Ehrhart.JetEnvelopeLocalGrowth.sourceTorusCoverPoint_mem_shrinkingBall_of_mem_box
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
open Ehrhart.JetEnvelopeLocalGrowth
open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
universe u v

theorem Ehrhart.JetEnvelopeLocalGrowth.sourceTorusCoverPoint_mem_shrinkingBall_of_mem_box
    {n : ℕ} {R t : ℝ}
    (hR : 0 < R)
    (q : WeightedTorusHilbert.LogTorus n)
    (hq : q ∈ sourceLocalTorusBox n (sourceLocalBoxRadius R t)) :
    dist (sourceTorusCoverPoint q)
        (0 : TorusCharacters.LogSpace n) <
      R * Real.exp (-t / 2) := by sorry
