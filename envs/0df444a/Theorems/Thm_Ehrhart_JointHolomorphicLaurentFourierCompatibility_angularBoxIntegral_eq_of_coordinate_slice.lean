-- Prove2me | Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularBoxIntegral_eq_of_coordinate_slice
-- name    : Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularBoxIntegral_eq_of_coordinate_slice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/875a45ee-0a3e-4dea-8d11-b380ccd85659
-- title:
--   Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularBoxIntegral_eq_of_coordinate_slice
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
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918

theorem Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularBoxIntegral_eq_of_coordinate_slice
    {n : ℕ} {g h : Space (n + 1) → ℂ}
    (hg : Continuous g) (hh : Continuous h)
    (i : Fin (n + 1))
    (hslice : ∀ y : Fin n → ℝ,
      (∫ t : ℝ in 0..1, g (i.insertNth t y)) =
        ∫ t : ℝ in 0..1, h (i.insertNth t y)) :
    (∫ t : Space (n + 1),
      g t ∂(angularBoxMeasure (n + 1))) =
      ∫ t : Space (n + 1),
        h t ∂(angularBoxMeasure (n + 1)) := by sorry
