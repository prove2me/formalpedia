-- Prove2me | Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_indexedMonomial_finite_sum_ae
-- name    : Ehrhart.JointHolomorphicLaurentFourierCompatibility.indexedMonomial_finite_sum_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/95f85b66-783a-4ccf-8239-fff7ebde65a2
-- title:
--   Ehrhart.JointHolomorphicLaurentFourierCompatibility.indexedMonomial_finite_sum_ae
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
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918

theorem Ehrhart.JointHolomorphicLaurentFourierCompatibility.indexedMonomial_finite_sum_ae
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (s : Finset (LatticeAsymptotics.monomialIndex K k))
    (c : LatticeAsymptotics.monomialIndex K k → ℂ) :
    (fun z : WeightedTorusHilbert.LogTorus n =>
      (∑ u ∈ s, c u •
        WeightedTorusHilbert.indexedMonomialLp
          K hk hφ hbounded u) z)
      =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
    (fun z =>
      ∑ u ∈ s, c u *
        WeightedTorusHilbert.torusMonomial
          (WeightedTorusHilbert.integerExponent K hk u) z) := by sorry
