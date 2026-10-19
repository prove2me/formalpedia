-- Prove2me | Theorems.Thm_Ehrhart_TorusNoncompactBochner_angularTorus_compact_form_curvature_le_adjoint_add_exterior
-- name    : Ehrhart.TorusNoncompactBochner.angularTorus_compact_form_curvature_le_adjoint_add_exterior
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/853189ec-9476-4045-a331-8d5c60117855
-- title:
--   Ehrhart.TorusNoncompactBochner.angularTorus_compact_form_curvature_le_adjoint_add_exterior
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
open Ehrhart.TorusNoncompactBochner
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.TorusNoncompactBochner.angularTorus_compact_form_curvature_le_adjoint_add_exterior
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    (∫ p : LogTorus n,
      angularTorusFormCurvatureDensity a W p
        ∂(angularWeightedTorusMeasure a)).re ≤
    (∫ p : LogTorus n,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p)
          ∂(angularWeightedTorusMeasure a)).re +
    (∫ p : LogTorus n,
      sourceTorusFormExteriorDerivativeDensity W p
        ∂(angularWeightedTorusMeasure a)).re := by sorry
