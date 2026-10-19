-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetDualGradientConcentration_ae_differentiableAt_of_locallyLipschitzOn_open
-- name    : Ehrhart.BergmanJetDualGradientConcentration.ae_differentiableAt_of_locallyLipschitzOn_open
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/e047fd29-f125-4149-a9d9-391d07ac18f7
-- title:
--   Ehrhart.BergmanJetDualGradientConcentration.ae_differentiableAt_of_locallyLipschitzOn_open
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
open Ehrhart.BergmanJetDualGradientConcentration
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentInteriorLegendre
open scoped ENNReal NNReal Topology

theorem Ehrhart.BergmanJetDualGradientConcentration.ae_differentiableAt_of_locallyLipschitzOn_open
    {n : ℕ} {s : Set (Space n)}
    (hs : IsOpen s) {f : Space n → ℝ}
    (hf : LocallyLipschitzOn s f) :
    ∀ᵐ x : Space n ∂(volume : Measure (Space n)),
      x ∈ s → DifferentiableAt ℝ f x := by sorry
