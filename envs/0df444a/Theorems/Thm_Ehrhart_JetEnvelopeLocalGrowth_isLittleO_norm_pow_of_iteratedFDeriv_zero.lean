-- Prove2me | Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_isLittleO_norm_pow_of_iteratedFDeriv_zero
-- name    : Ehrhart.JetEnvelopeLocalGrowth.isLittleO_norm_pow_of_iteratedFDeriv_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/aba0af56-edef-49e9-a5a0-a5896576c3fa
-- title:
--   Ehrhart.JetEnvelopeLocalGrowth.isLittleO_norm_pow_of_iteratedFDeriv_zero
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
open Ehrhart.JetEnvelopeLocalGrowth
open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
universe u v

theorem Ehrhart.JetEnvelopeLocalGrowth.isLittleO_norm_pow_of_iteratedFDeriv_zero
    {E : Type u} {F : Type (max u v)}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E → F) (hf : ContDiff ℂ ⊤ f)
    (p : E) (j : ℕ)
    (hzero : ∀ i : ℕ, i ≤ j → iteratedFDeriv ℂ i f p = 0) :
    (fun z : E => f z - f p) =o[𝓝 p]
      (fun z : E => ‖z - p‖ ^ j) := by sorry
