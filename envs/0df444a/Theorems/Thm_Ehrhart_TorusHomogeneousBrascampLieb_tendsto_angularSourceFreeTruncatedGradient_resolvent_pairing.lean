-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_tendsto_angularSourceFreeTruncatedGradient_resolvent_pairing
-- name    : Ehrhart.TorusHomogeneousBrascampLieb.tendsto_angularSourceFreeTruncatedGradient_resolvent_pairing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:08.235634+00:00
-- url     : https://prove2.me/theorems/b746ee81-bd13-43a3-9fdd-728fcfbe484b
-- title:
--   Ehrhart.TorusHomogeneousBrascampLieb.tendsto_angularSourceFreeTruncatedGradient_resolvent_pairing
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
open Ehrhart.TorusHomogeneousBrascampLieb
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBrascampLieb
open MatrixTorusDolbeaultGraph TorusDeckGraphAdjoint TorusFriedrichsCutoff
open RadialPhysicalVelocityCompactGraph RadialPhysicalInverseSquareRootEnergy
open RadialPhysicalResolventRootCutoffPairing RadialPhysicalResolventDefectReduction
open TorusHomogeneousWeakResolventRootCoercivity
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff

theorem Ehrhart.TorusHomogeneousBrascampLieb.tendsto_angularSourceFreeTruncatedGradient_resolvent_pairing
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (g : angularWeightedScalarL2 a) :
    Tendsto
      (fun m : ℕ =>
        @inner ℂ (angularWeightedFormL2 a) _
          (WithLp.snd
            (angularWeakDolbeaultResolvent a g :
              angularDolbeaultGraphAmbient a))
          (angularSourceFreeTruncatedGradientL2 ha hU hperiod hu m))
      atTop
      (nhds
        (@inner ℂ (angularWeightedScalarL2 a) _
          (g - angularWeakScalarResolventCLM a g)
          (hu.toLp (torusScalarRepresentative U)))) := by sorry
