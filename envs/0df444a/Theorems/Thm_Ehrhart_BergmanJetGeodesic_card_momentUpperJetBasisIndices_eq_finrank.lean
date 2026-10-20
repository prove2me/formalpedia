-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetGeodesic_card_momentUpperJetBasisIndices_eq_finrank
-- name    : Ehrhart.BergmanJetGeodesic.card_momentUpperJetBasisIndices_eq_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/9a04a4d4-65e2-4a71-af08-e1ee675cfacc
-- title:
--   Ehrhart.BergmanJetGeodesic.card_momentUpperJetBasisIndices_eq_finrank
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
open Ehrhart.BergmanJetGeodesic
open Set Function Filter MeasureTheory Module
open BergmanMonomials LatticeAsymptotics AdaptedBergmanBasis MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetBasis JetAdaptedOrthonormalBasis
open GenuineJetAdaptedBasisCounting
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology

theorem Ehrhart.BergmanJetGeodesic.card_momentUpperJetBasisIndices_eq_finrank
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (j : ℕ) :
    (momentUpperJetBasisIndices K hk F htransport p j).card =
      Module.finrank ℂ
        (momentJetFiltration K hk F htransport p j) := by sorry
