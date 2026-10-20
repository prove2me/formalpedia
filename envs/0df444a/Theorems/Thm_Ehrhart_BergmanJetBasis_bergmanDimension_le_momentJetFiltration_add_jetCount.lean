-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetBasis_bergmanDimension_le_momentJetFiltration_add_jetCount
-- name    : Ehrhart.BergmanJetBasis.bergmanDimension_le_momentJetFiltration_add_jetCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/50198470-3797-448d-94f4-0fc680ba8653
-- title:
--   Ehrhart.BergmanJetBasis.bergmanDimension_le_momentJetFiltration_add_jetCount
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
open Ehrhart.BergmanJetBasis
open Set Function Filter MeasureTheory Module
open BergmanMonomials LatticeAsymptotics WeightedTorusHilbert AdaptedBergmanBasis MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology

theorem Ehrhart.BergmanJetBasis.bergmanDimension_le_momentJetFiltration_add_jetCount
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {j : ℕ} (hj : 0 < j) :
    bergmanDimension K k ≤
      Module.finrank ℂ (momentJetFiltration
        K hk F htransport p j) +
        (n + j - 1).choose n := by sorry
