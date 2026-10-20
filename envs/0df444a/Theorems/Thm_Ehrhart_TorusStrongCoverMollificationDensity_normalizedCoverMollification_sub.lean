-- Prove2me | Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollification_sub
-- name    : Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollification_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/0a8721c8-2fde-41b4-9157-772b75961558
-- title:
--   Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollification_sub
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
open Ehrhart.TorusStrongCoverMollificationDensity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity MatrixTorusBochnerCoreApproximation
open TorusWeakDolbeaultMollification TorusMollificationLocalL2Bounds TorusStrongCoverMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollification_sub
    {n : ℕ} {g h : LogSpace n → ℂ}
    (hg : MemLp g 2 (volume : Measure (LogSpace n)))
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) (x : LogSpace n) :
    normalizedCoverMollification (fun y => g y - h y) k x =
      normalizedCoverMollification g k x -
        normalizedCoverMollification h k x := by sorry
