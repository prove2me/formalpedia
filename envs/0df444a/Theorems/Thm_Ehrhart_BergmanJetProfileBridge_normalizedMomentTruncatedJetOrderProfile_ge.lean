-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetProfileBridge_normalizedMomentTruncatedJetOrderProfile_ge
-- name    : Ehrhart.BergmanJetProfileBridge.normalizedMomentTruncatedJetOrderProfile_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/6afe423e-6df7-4751-9217-a462cb150912
-- title:
--   Ehrhart.BergmanJetProfileBridge.normalizedMomentTruncatedJetOrderProfile_ge
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
open Ehrhart.BergmanJetProfileBridge
open Set Function Filter MeasureTheory Module InnerProductSpace
open SupportFunction BergmanMonomials LatticeAsymptotics WeightedTorusHilbert AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity BergmanJetBasis
open BergmanJetGeodesic BergmanDiagonalBasisIndependence
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology

theorem Ehrhart.BergmanJetProfileBridge.normalizedMomentTruncatedJetOrderProfile_ge
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (t : ℝ) :
    (((Nat.floor (t * (k : ℝ)) : ℕ) : ℝ) *
          (bergmanDimension K k : ℝ) -
        (((n + Nat.floor (t * (k : ℝ))).choose
          (n + 1) : ℕ) : ℝ)) /
        ((k : ℝ) * (bergmanDimension K k : ℝ)) ≤
      normalizedMomentTruncatedJetOrderProfile
        K F htransport p t k := by sorry
