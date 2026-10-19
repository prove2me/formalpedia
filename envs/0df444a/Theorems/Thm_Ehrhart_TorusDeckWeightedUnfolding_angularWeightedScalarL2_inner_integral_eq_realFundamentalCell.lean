-- Prove2me | Theorems.Thm_Ehrhart_TorusDeckWeightedUnfolding_angularWeightedScalarL2_inner_integral_eq_realFundamentalCell
-- name    : Ehrhart.TorusDeckWeightedUnfolding.angularWeightedScalarL2_inner_integral_eq_realFundamentalCell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/5f432e9c-c150-4c18-8089-fe63eff78dbf
-- title:
--   Ehrhart.TorusDeckWeightedUnfolding.angularWeightedScalarL2_inner_integral_eq_realFundamentalCell
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
open Ehrhart.TorusDeckWeightedUnfolding
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open WeightedTorusBochner TorusWeightedBaseAE
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold

theorem Ehrhart.TorusDeckWeightedUnfolding.angularWeightedScalarL2_inner_integral_eq_realFundamentalCell
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    (f : angularWeightedScalarL2 a)
    {G : LogTorus n → ℂ}
    (hG : Continuous G) :
    (∫ q : LogTorus n,
      @inner ℂ ℂ _ (f q) (G q)
        ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularUnweightedTorusIntegrand a
          (fun q : LogTorus n => @inner ℂ ℂ _ (f q) (G q))
          (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by sorry
