-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_eventually_momentJetBasisRepresentative_local_bound
-- name    : Ehrhart.BergmanJetLocalGrowth.eventually_momentJetBasisRepresentative_local_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:09.94113+00:00
-- url     : https://prove2.me/theorems/d6fea377-9dda-4b4c-b8b1-584f30836ad2
-- title:
--   Ehrhart.BergmanJetLocalGrowth.eventually_momentJetBasisRepresentative_local_bound
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

theorem Ehrhart.BergmanJetLocalGrowth.eventually_momentJetBasisRepresentative_local_bound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (R : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∀ (hk : 0 < k)
      (i : Fin (bergmanDimension K k))
      (z : TorusCharacters.LogSpace n),
      z ∈ Metric.ball p R →
        ‖momentHolomorphicRepresentative K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p i) z‖ ≤
          Real.sqrt
            (Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
              globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)) := by sorry
