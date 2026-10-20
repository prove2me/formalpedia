-- Prove2me | Theorems.Thm_Ehrhart_TorusWeightedDensityConvolutionDivergence_holomorphicCoordinate_normalizedCoverMollification_eq_kernel
-- name    : Ehrhart.TorusWeightedDensityConvolutionDivergence.holomorphicCoordinate_normalizedCoverMollification_eq_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/49cd475f-bcc7-4389-8040-c2c10a85112e
-- title:
--   Ehrhart.TorusWeightedDensityConvolutionDivergence.holomorphicCoordinate_normalizedCoverMollification_eq_kernel
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

theorem Ehrhart.TorusWeightedDensityConvolutionDivergence.holomorphicCoordinate_normalizedCoverMollification_eq_kernel
    {n : ℕ} {g : LogSpace n → ℂ}
    (hg : LocallyIntegrable g (volume : Measure (LogSpace n)))
    (k : ℕ) (x : LogSpace n) (j : Fin n) :
    holomorphicCoordinate (normalizedCoverMollification g k) x j =
      -(∫ y : LogSpace n,
        g y *
          conj (barPartialCoordinate
            (fun z : LogSpace n =>
              ((complexShrinkingBump (n := n) k).normed
                (volume : Measure (LogSpace n)) (x - z) : ℂ)) y j)
        ∂(volume : Measure (LogSpace n))) := by sorry
