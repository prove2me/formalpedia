-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetRoundedMonomialObservableConvergence_momentNormalizedPhase_dualGradient_maximizer
-- name    : Ehrhart.BergmanJetRoundedMonomialObservableConvergence.momentNormalizedPhase_dualGradient_maximizer
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/59c6ca3e-03a9-4ac1-a9f9-7576e18397c1
-- title:
--   Ehrhart.BergmanJetRoundedMonomialObservableConvergence.momentNormalizedPhase_dualGradient_maximizer
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
open Ehrhart.BergmanJetRoundedMonomialObservableConvergence
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open BergmanJetPhaseLaplace BergmanJetDualPhaseConcentration
open scoped ENNReal NNReal Topology

theorem Ehrhart.BergmanJetRoundedMonomialObservableConvergence.momentNormalizedPhase_dualGradient_maximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u) :
    ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F)
          (SpatialBergmanFatouScheffe.actualGradient
            (legendreTransform F.potential) u) := by sorry
