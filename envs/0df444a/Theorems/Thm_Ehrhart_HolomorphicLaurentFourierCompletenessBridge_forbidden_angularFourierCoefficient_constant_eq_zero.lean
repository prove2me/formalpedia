-- Prove2me | Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_forbidden_angularFourierCoefficient_constant_eq_zero
-- name    : Ehrhart.HolomorphicLaurentFourierCompletenessBridge.forbidden_angularFourierCoefficient_constant_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/7611f619-dcc3-4476-b39a-606e720c047e
-- title:
--   Ehrhart.HolomorphicLaurentFourierCompletenessBridge.forbidden_angularFourierCoefficient_constant_eq_zero
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

theorem Ehrhart.HolomorphicLaurentFourierCompletenessBridge.forbidden_angularFourierCoefficient_constant_eq_zero
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u)
    (hu : u ∉ interior K.carrier)
    (c : ℂ)
    (hcoefficient :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        angularFourierCoefficient φ f m x =
          c * WeightedTorusHilbert.radialCharacter m x) :
    c = 0 := by sorry
