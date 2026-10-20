-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_moment_iteratedFDeriv_coordinate_eq_zero_of_mem_jetFiltration
-- name    : Ehrhart.BergmanJetLocalGrowth.moment_iteratedFDeriv_coordinate_eq_zero_of_mem_jetFiltration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:09.94113+00:00
-- url     : https://prove2.me/theorems/c655745f-d563-41aa-98e2-dfa383be9016
-- title:
--   Ehrhart.BergmanJetLocalGrowth.moment_iteratedFDeriv_coordinate_eq_zero_of_mem_jetFiltration
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

theorem Ehrhart.BergmanJetLocalGrowth.moment_iteratedFDeriv_coordinate_eq_zero_of_mem_jetFiltration
    {n k r : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport)
    (q : Fin r → Fin n) (α : Fin n → ℕ)
    (hdegree : (∑ i, α i) = r)
    (hcount : ∀ i : Fin n,
      Fintype.card {a : Fin r // q a = i} = α i)
    (hs : s ∈ momentJetFiltration
      K hk F htransport p (r + 1)) :
    (iteratedFDeriv ℂ r
      (momentHolomorphicRepresentative K hk F htransport s) p)
      (fun a => Pi.single (q a) (1 : ℂ)) = 0 := by sorry
