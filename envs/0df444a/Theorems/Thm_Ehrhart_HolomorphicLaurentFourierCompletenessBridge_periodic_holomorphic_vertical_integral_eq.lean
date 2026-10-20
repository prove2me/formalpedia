-- Prove2me | Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_periodic_holomorphic_vertical_integral_eq
-- name    : Ehrhart.HolomorphicLaurentFourierCompletenessBridge.periodic_holomorphic_vertical_integral_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/769eb8b1-9f8e-4a08-bff8-5ae7a6cf0f8b
-- title:
--   Ehrhart.HolomorphicLaurentFourierCompletenessBridge.periodic_holomorphic_vertical_integral_eq
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
open Ehrhart.HolomorphicLaurentFourierCompletenessBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13449
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13452

theorem Ehrhart.HolomorphicLaurentFourierCompletenessBridge.periodic_holomorphic_vertical_integral_eq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hperiod : Function.Periodic f logarithmicPeriod)
    (a b : ℝ) :
    (∫ t : ℝ in 0..2 * Real.pi,
      f ((b : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ in 0..2 * Real.pi,
        f ((a : ℂ) + (t : ℂ) * Complex.I) := by sorry
