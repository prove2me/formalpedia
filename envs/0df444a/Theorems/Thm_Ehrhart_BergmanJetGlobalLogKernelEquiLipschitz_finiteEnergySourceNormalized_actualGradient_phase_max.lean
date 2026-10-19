-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_finiteEnergySourceNormalized_actualGradient_phase_max
-- name    : Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.finiteEnergySourceNormalized_actualGradient_phase_max
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/022dd3e3-d461-4a07-86ff-27bbe5fb5904
-- title:
--   Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.finiteEnergySourceNormalized_actualGradient_phase_max
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
open Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics BergmanMonomials LatticeAsymptotics LaurentJetSeparatedness
open GlobalBergmanKernelBound MomentMinimizer MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation MomentRegularity BergmanJetBasis MomentWeakGlobalKernel
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.finiteEnergySourceNormalized_actualGradient_phase_max
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (z : Space n) :
    phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        (momentNormalizedPotential F) z ≤
      phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        (momentNormalizedPotential F) x := by sorry
