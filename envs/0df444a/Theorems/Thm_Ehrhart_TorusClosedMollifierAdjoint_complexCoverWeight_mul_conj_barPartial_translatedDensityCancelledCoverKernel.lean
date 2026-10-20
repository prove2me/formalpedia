-- Prove2me | Theorems.Thm_Ehrhart_TorusClosedMollifierAdjoint_complexCoverWeight_mul_conj_barPartial_translatedDensityCancelledCoverKernel
-- name    : Ehrhart.TorusClosedMollifierAdjoint.complexCoverWeight_mul_conj_barPartial_translatedDensityCancelledCoverKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/051d251b-5ba3-46c1-865e-60eeef56344e
-- title:
--   Ehrhart.TorusClosedMollifierAdjoint.complexCoverWeight_mul_conj_barPartial_translatedDensityCancelledCoverKernel
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
open Ehrhart.TorusClosedMollifierAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open TorusDensityAdaptedWeightedAdjoint
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusClosedMollifierAdjoint.complexCoverWeight_mul_conj_barPartial_translatedDensityCancelledCoverKernel
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 1 (angularCoverPotential a))
    (k : ℕ) (x y : LogSpace n) (j : Fin n) :
    complexCoverWeight (angularCoverPotential a) y *
      conj (barPartialCoordinate
        (fun z : LogSpace n =>
          (translatedDensityCancelledCoverKernel a k x z : ℂ)) y j) =
      conj (barPartialCoordinate
        (fun z : LogSpace n =>
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - z) : ℂ)) y j) +
      ((complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) : ℂ) *
        holomorphicCoordinate
          (fun z : LogSpace n =>
            (angularCoverPotential a z : ℂ)) y j := by sorry
