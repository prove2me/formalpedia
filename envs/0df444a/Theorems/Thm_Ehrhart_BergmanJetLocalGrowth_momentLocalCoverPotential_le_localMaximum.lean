-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_momentLocalCoverPotential_le_localMaximum
-- name    : Ehrhart.BergmanJetLocalGrowth.momentLocalCoverPotential_le_localMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:09.94113+00:00
-- url     : https://prove2.me/theorems/802359b0-78ee-4fb8-8cd9-ab76422bfd5f
-- title:
--   Ehrhart.BergmanJetLocalGrowth.momentLocalCoverPotential_le_localMaximum
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
open Ehrhart.BergmanJetLocalGrowth
open Set Function Filter MeasureTheory Module Metric Asymptotics
open BergmanMonomials BergmanDiagonalBasisIndependence GlobalBergmanKernelBound AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetBasis MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge
open BergmanJetRealGeodesic JetEnvelopeLocalGrowth LaurentJetMultiplicityBridge
open scoped BigOperators Topology ENNReal InnerProductSpace

theorem Ehrhart.BergmanJetLocalGrowth.momentLocalCoverPotential_le_localMaximum
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (p : TorusCharacters.LogSpace n) (R : ℝ)
    (z : TorusCharacters.LogSpace n)
    (hz : z ∈ Metric.closedBall p R) :
    momentLocalCoverPotential K F z ≤
      momentLocalPotentialMaximum K F p R := by sorry
