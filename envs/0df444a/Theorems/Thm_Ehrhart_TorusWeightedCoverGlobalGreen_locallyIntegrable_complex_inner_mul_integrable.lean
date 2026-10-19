-- Prove2me | Theorems.Thm_Ehrhart_TorusWeightedCoverGlobalGreen_locallyIntegrable_complex_inner_mul_integrable
-- name    : Ehrhart.TorusWeightedCoverGlobalGreen.locallyIntegrable_complex_inner_mul_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/2a9a449c-d999-4137-9d0e-b849d86e1c59
-- title:
--   Ehrhart.TorusWeightedCoverGlobalGreen.locallyIntegrable_complex_inner_mul_integrable
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
open Ehrhart.TorusWeightedCoverGlobalGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold

theorem Ehrhart.TorusWeightedCoverGlobalGreen.locallyIntegrable_complex_inner_mul_integrable
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [T2Space E]
    {μ : Measure E} {F G : E → ℂ}
    (hF : LocallyIntegrable F μ)
    (hG : Continuous G)
    (hGcompact : HasCompactSupport G) :
    Integrable (fun z => @inner ℂ ℂ _ (F z) (G z)) μ := by sorry
