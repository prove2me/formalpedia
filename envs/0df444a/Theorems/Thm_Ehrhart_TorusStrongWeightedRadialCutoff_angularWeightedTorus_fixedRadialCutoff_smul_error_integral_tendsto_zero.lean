-- Prove2me | Theorems.Thm_Ehrhart_TorusStrongWeightedRadialCutoff_angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
-- name    : Ehrhart.TorusStrongWeightedRadialCutoff.angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/f26513ab-51cf-4972-bc71-6e941ac82676
-- title:
--   Ehrhart.TorusStrongWeightedRadialCutoff.angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
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
open Ehrhart.TorusStrongWeightedRadialCutoff
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusStrongWeightedRadialCutoff.angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℕ → LogTorus n → E}
    {f : LogTorus n → E}
    (hlocal : ∀ (k : ℕ) {S : Set (LogTorus n)}, IsCompact S →
      IntegrableOn
        (fun q : LogTorus n => ‖F k q - f q‖ ^ 2)
        S (angularWeightedTorusMeasure a))
    (hconv : ∀ {S : Set (LogTorus n)}, IsCompact S →
      Tendsto
        (fun k : ℕ =>
          ∫ q in S, ‖F k q - f q‖ ^ 2
            ∂(angularWeightedTorusMeasure a))
        atTop (nhds 0))
    (m : ℕ) :
    Tendsto
      (fun k : ℕ =>
        ∫ q : LogTorus n,
          ‖(sourceRadialCutoff m q : ℂ) • F k q -
            (sourceRadialCutoff m q : ℂ) • f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by sorry
