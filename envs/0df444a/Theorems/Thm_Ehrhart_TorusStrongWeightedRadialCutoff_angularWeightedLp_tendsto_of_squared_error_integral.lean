-- Prove2me | Theorems.Thm_Ehrhart_TorusStrongWeightedRadialCutoff_angularWeightedLp_tendsto_of_squared_error_integral
-- name    : Ehrhart.TorusStrongWeightedRadialCutoff.angularWeightedLp_tendsto_of_squared_error_integral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/ed2d160d-1d7d-4e8a-b859-b30b43295bed
-- title:
--   Ehrhart.TorusStrongWeightedRadialCutoff.angularWeightedLp_tendsto_of_squared_error_integral
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

theorem Ehrhart.TorusStrongWeightedRadialCutoff.angularWeightedLp_tendsto_of_squared_error_integral
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {F : ℕ → LogTorus n → E} {f : LogTorus n → E}
    (hF : ∀ k : ℕ, MemLp (F k) 2 (angularWeightedTorusMeasure a))
    (hf : MemLp f 2 (angularWeightedTorusMeasure a))
    (hconv : Tendsto
      (fun k : ℕ =>
        ∫ q : LogTorus n, ‖F k q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0)) :
    Tendsto
      (fun k : ℕ => (hF k).toLp (F k))
      atTop (nhds (hf.toLp f)) := by sorry
