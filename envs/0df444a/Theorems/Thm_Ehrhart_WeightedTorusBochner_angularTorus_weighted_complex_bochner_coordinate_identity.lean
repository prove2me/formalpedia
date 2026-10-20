-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusBochner_angularTorus_weighted_complex_bochner_coordinate_identity
-- name    : Ehrhart.WeightedTorusBochner.angularTorus_weighted_complex_bochner_coordinate_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:57.23131+00:00
-- url     : https://prove2.me/theorems/4be0c6eb-3287-4585-93e8-a44720b219c1
-- title:
--   Ehrhart.WeightedTorusBochner.angularTorus_weighted_complex_bochner_coordinate_identity
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
open Ehrhart.WeightedTorusBochner
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.WeightedTorusBochner.angularTorus_weighted_complex_bochner_coordinate_identity
    {n : ℕ} {a : LogTorus n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G)
    (hFp : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hGp : ∀ q : Fin n → ℤ,
      Function.Periodic G
        (TorusCharacters.imaginaryShift q))
    (hGc : HasCompactSupport (torusScalarRepresentative G))
    (i j : Fin n) :
    (∫ p : LogTorus n,
      angularTorusWeightedHolomorphicDerivative a F i p *
        conj (angularTorusWeightedHolomorphicDerivative a G j p)
      ∂(angularWeightedTorusMeasure a)) =
    ∫ p : LogTorus n,
      (sourceTorusBarPartial F j p *
        conj (sourceTorusBarPartial G i p) +
       (torusScalarRepresentative F p *
          angularTorusComplexHessian a i j p) *
            conj (torusScalarRepresentative G p))
      ∂(angularWeightedTorusMeasure a) := by sorry
