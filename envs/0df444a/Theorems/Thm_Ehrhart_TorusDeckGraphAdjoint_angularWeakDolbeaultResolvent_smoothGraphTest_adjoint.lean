-- Prove2me | Theorems.Thm_Ehrhart_TorusDeckGraphAdjoint_angularWeakDolbeaultResolvent_smoothGraphTest_adjoint
-- name    : Ehrhart.TorusDeckGraphAdjoint.angularWeakDolbeaultResolvent_smoothGraphTest_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/56bfff90-aa24-4d99-b8d9-238f87f722f9
-- title:
--   Ehrhart.TorusDeckGraphAdjoint.angularWeakDolbeaultResolvent_smoothGraphTest_adjoint
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

theorem Ehrhart.TorusDeckGraphAdjoint.angularWeakDolbeaultResolvent_smoothGraphTest_adjoint
    {n : ℕ} (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hFcont : ContDiff ℝ 3 F)
    (hFperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hFcompact : HasCompactSupport (torusScalarRepresentative F))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd
        (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a))
      (angularBarPartialL2OfRepresentative a F hD) =
    @inner ℂ (angularWeightedScalarL2 a) _
      (f - angularWeakScalarResolventCLM a f)
      (angularScalarL2OfRepresentative a F hF) := by sorry
