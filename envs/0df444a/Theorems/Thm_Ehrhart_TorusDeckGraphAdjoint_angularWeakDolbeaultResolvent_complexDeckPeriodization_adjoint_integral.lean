-- Prove2me | Theorems.Thm_Ehrhart_TorusDeckGraphAdjoint_angularWeakDolbeaultResolvent_complexDeckPeriodization_adjoint_integral
-- name    : Ehrhart.TorusDeckGraphAdjoint.angularWeakDolbeaultResolvent_complexDeckPeriodization_adjoint_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/45e07f44-b3b0-4de6-abca-93029ac3be6c
-- title:
--   Ehrhart.TorusDeckGraphAdjoint.angularWeakDolbeaultResolvent_complexDeckPeriodization_adjoint_integral
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
open Ehrhart.TorusDeckGraphAdjoint
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault WeightedTorusBrascampLieb TorusDeckPeriodization TorusDeckCompactSupport
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusDeckGraphAdjoint.angularWeakDolbeaultResolvent_complexDeckPeriodization_adjoint_integral
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ) :
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) q)
        (torusFunctionBarPartialRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) =
    (∫ q : LogTorus n,
      @inner ℂ ℂ _
        ((f - angularWeakScalarResolventCLM a f) q)
        (torusScalarRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) := by sorry
