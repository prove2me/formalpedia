-- Prove2me | Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollificationL2_toLp
-- name    : Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollificationL2_toLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/4f257a77-2a52-4b79-afe1-572415b17b45
-- title:
--   Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollificationL2_toLp
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

theorem Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollificationL2_toLp
    {n : ℕ} {g : LogSpace n → ℂ}
    (hg : MemLp g 2 (volume : Measure (LogSpace n)))
    (k : ℕ) :
    normalizedCoverMollificationL2 k (hg.toLp g) =
      (normalizedCoverMollification_memLp hg k).toLp
        (normalizedCoverMollification g k) := by sorry
