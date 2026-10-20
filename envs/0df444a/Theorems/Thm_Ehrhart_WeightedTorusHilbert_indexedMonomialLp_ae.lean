-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusHilbert_indexedMonomialLp_ae
-- name    : Ehrhart.WeightedTorusHilbert.indexedMonomialLp_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/ca84e35b-dd82-4cde-ae26-4a193c903190
-- title:
--   Ehrhart.WeightedTorusHilbert.indexedMonomialLp_ae
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
open Set MeasureTheory Filter
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
open Ehrhart.WeightedTorusHilbert
attribute [local instance] Ehrhart.WeightedTorusHilbert._p2m_local_instance_3610026555_1046
attribute [local instance] Ehrhart.WeightedTorusHilbert._p2m_local_instance_3610026555_1049

theorem Ehrhart.WeightedTorusHilbert.indexedMonomialLp_ae {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (u : LatticeAsymptotics.monomialIndex K k) :
    (indexedMonomialLp K hk hφ hbounded u : LogTorus n → ℂ)
      =ᵐ[weightedTorusMeasure k φ]
        torusMonomial (integerExponent K hk u) := by sorry
