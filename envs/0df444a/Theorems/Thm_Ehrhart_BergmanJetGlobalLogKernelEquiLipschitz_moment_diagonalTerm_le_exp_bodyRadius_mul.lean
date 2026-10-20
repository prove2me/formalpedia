-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_moment_diagonalTerm_le_exp_bodyRadius_mul
-- name    : Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.moment_diagonalTerm_le_exp_bodyRadius_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/5bc0747d-41ce-4d5f-9c11-9772a692177b
-- title:
--   Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.moment_diagonalTerm_le_exp_bodyRadius_mul
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

theorem Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.moment_diagonalTerm_le_exp_bodyRadius_mul
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    (x y : Space n) :
    diagonalTerm K k (momentNormalizedPotential F) u x ≤
      Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
        diagonalTerm K k (momentNormalizedPotential F) u y := by sorry
