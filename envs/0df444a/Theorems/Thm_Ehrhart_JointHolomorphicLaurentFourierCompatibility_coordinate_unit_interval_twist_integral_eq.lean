-- Prove2me | Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_coordinate_unit_interval_twist_integral_eq
-- name    : Ehrhart.JointHolomorphicLaurentFourierCompatibility.coordinate_unit_interval_twist_integral_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/7d842bf7-2caa-4742-aada-1640a103c094
-- title:
--   Ehrhart.JointHolomorphicLaurentFourierCompatibility.coordinate_unit_interval_twist_integral_eq
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

theorem Ehrhart.JointHolomorphicLaurentFourierCompatibility.coordinate_unit_interval_twist_integral_eq {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m : Fin n → ℤ)
    (ζ : TorusCharacters.LogSpace n)
    (i : Fin n) (a b : ℝ) :
    (∫ t : ℝ in 0..1,
      globalLaurentTwist F m
        (fun j => if j = i
          then (b : ℂ) +
            (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
          else ζ j)) =
      ∫ t : ℝ in 0..1,
        globalLaurentTwist F m
          (fun j => if j = i
            then (a : ℂ) +
              (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
            else ζ j) := by sorry
