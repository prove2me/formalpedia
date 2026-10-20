-- Prove2me | Theorems.Thm_Ehrhart_TorusWeightedDensityConvolutionDivergence_normalizedCoverMollification_eq_kernel_integral
-- name    : Ehrhart.TorusWeightedDensityConvolutionDivergence.normalizedCoverMollification_eq_kernel_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/7a89609b-35b4-4cba-bdbe-fb5446a0512e
-- title:
--   Ehrhart.TorusWeightedDensityConvolutionDivergence.normalizedCoverMollification_eq_kernel_integral
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
open Ehrhart.TorusWeightedDensityConvolutionDivergence
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters DolbeaultRegularity
open DolbeaultGraphDistributionBridge WeightedDolbeaultBochnerIdentity
open TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusWeightedDensityConvolutionDivergence.normalizedCoverMollification_eq_kernel_integral
    {n : ℕ} (g : LogSpace n → ℂ)
    (k : ℕ) (x : LogSpace n) :
    normalizedCoverMollification g k x =
      ∫ y : LogSpace n,
        g y *
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - y) : ℂ)
        ∂(volume : Measure (LogSpace n)) := by sorry
