-- Prove2me | Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_mFourierCoefficient_coverRepresentative_eq_radial
-- name    : Ehrhart.JointHolomorphicLaurentFourierCompatibility.mFourierCoefficient_coverRepresentative_eq_radial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/e0f3b95b-8baf-404f-b782-09e5bd82b347
-- title:
--   Ehrhart.JointHolomorphicLaurentFourierCompatibility.mFourierCoefficient_coverRepresentative_eq_radial
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

theorem Ehrhart.JointHolomorphicLaurentFourierCompatibility.mFourierCoefficient_coverRepresentative_eq_radial
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m : Fin n → ℤ) (x : Space n) :
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m =
      UnitAddTorus.mFourierCoeff
          (coverRepresentative F 0) m *
        WeightedTorusHilbert.radialCharacter m x := by sorry
