-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellWeakAdjointFunctional_smoothGraph_zero
-- name    : Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellWeakAdjointFunctional_smoothGraph_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:52.714743+00:00
-- url     : https://prove2.me/theorems/cfbe409d-cb46-446d-967e-816ed24db5ef
-- title:
--   Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellWeakAdjointFunctional_smoothGraph_zero
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
open Ehrhart.WeightedTorusClosedGraphWeakBridge
open Set Function MeasureTheory Filter
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
  Manifold ContDiff

theorem Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellWeakAdjointFunctional_smoothGraph_zero
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ) (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF₁ : ContDiff ℝ 1 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (weightedTorusMeasure k φ))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (weightedTorusMeasure k φ)) (j : Fin n) :
    weightedCellWeakAdjointFunctional (k := k)
      hφ b hψ hψcompact j
        (WithLp.toLp 2
          (torusScalarL2OfRepresentative φ F hF,
           torusFunctionBarPartialL2 φ F hD)) = 0 := by sorry
