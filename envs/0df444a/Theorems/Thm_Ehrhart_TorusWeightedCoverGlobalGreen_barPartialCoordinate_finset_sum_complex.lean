-- Prove2me | Theorems.Thm_Ehrhart_TorusWeightedCoverGlobalGreen_barPartialCoordinate_finset_sum_complex
-- name    : Ehrhart.TorusWeightedCoverGlobalGreen.barPartialCoordinate_finset_sum_complex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/5b9fc7c7-e5cb-414a-a37f-344d044d5e08
-- title:
--   Ehrhart.TorusWeightedCoverGlobalGreen.barPartialCoordinate_finset_sum_complex
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

theorem Ehrhart.TorusWeightedCoverGlobalGreen.barPartialCoordinate_finset_sum_complex
    {n : ℕ} {ι : Type*} (s : Finset ι)
    (ψ : ι → LogSpace n → ℂ)
    (hψ : ∀ i ∈ s, ContDiff ℝ 1 (ψ i))
    (j : Fin n) (z : LogSpace n) :
    barPartialCoordinate (fun w => ∑ i ∈ s, ψ i w) z j =
      ∑ i ∈ s, barPartialCoordinate (ψ i) z j := by sorry
