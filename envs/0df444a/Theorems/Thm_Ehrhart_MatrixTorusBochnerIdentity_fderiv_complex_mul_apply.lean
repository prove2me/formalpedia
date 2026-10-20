-- Prove2me | Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_fderiv_complex_mul_apply
-- name    : Ehrhart.MatrixTorusBochnerIdentity.fderiv_complex_mul_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:57.23131+00:00
-- url     : https://prove2.me/theorems/69f625da-4738-4b6d-a888-c08425e8e76e
-- title:
--   Ehrhart.MatrixTorusBochnerIdentity.fderiv_complex_mul_apply
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
open Ehrhart.MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.MatrixTorusBochnerIdentity.fderiv_complex_mul_apply
    {n : ℕ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (fun w => F w * G w) z) v =
      F z * (fderiv ℝ G z) v +
        G z * (fderiv ℝ F z) v := by sorry
