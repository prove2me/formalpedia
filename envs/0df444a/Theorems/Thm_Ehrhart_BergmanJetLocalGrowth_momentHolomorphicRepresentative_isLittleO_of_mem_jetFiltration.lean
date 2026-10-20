-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_momentHolomorphicRepresentative_isLittleO_of_mem_jetFiltration
-- name    : Ehrhart.BergmanJetLocalGrowth.momentHolomorphicRepresentative_isLittleO_of_mem_jetFiltration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:09.94113+00:00
-- url     : https://prove2.me/theorems/5203b255-ddd9-4ca7-8eb8-914d18645f8b
-- title:
--   Ehrhart.BergmanJetLocalGrowth.momentHolomorphicRepresentative_isLittleO_of_mem_jetFiltration
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

theorem Ehrhart.BergmanJetLocalGrowth.momentHolomorphicRepresentative_isLittleO_of_mem_jetFiltration
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport)
    (j : ℕ)
    (hs : s ∈ momentJetFiltration
      K hk F htransport p (j + 1)) :
    (fun z : TorusCharacters.LogSpace n =>
      momentHolomorphicRepresentative K hk F htransport s z -
        momentHolomorphicRepresentative K hk F htransport s p)
      =o[𝓝 p]
        (fun z : TorusCharacters.LogSpace n => ‖z - p‖ ^ j) := by sorry
