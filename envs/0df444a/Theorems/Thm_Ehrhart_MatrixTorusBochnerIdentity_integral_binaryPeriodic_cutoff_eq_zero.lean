-- Prove2me | Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_integral_binaryPeriodic_cutoff_eq_zero
-- name    : Ehrhart.MatrixTorusBochnerIdentity.integral_binaryPeriodic_cutoff_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:55.424275+00:00
-- url     : https://prove2.me/theorems/5e66ccf2-3a97-45bc-b035-d4598863f854
-- title:
--   Ehrhart.MatrixTorusBochnerIdentity.integral_binaryPeriodic_cutoff_eq_zero
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

theorem Ehrhart.MatrixTorusBochnerIdentity.integral_binaryPeriodic_cutoff_eq_zero
    {n : ℕ} {κ : Space n → ℝ}
    (hκ : Continuous κ)
    (hκcompact : HasCompactSupport κ)
    (houtside : ∀ t : Space n,
      t ∉ Set.univ.pi
        (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) → κ t = 0)
    (hcancel : ∀ t : Space n,
      (∀ i : Fin n, 0 ≤ t i) →
      (∀ i : Fin n, t i ≤ 1) →
      (∑ q : Fin n → Bool,
        κ (binaryAngularFundamentalBase q + t)) = 0)
    {g : Space n → ℂ}
    (hg : Continuous g)
    (hperiod : ∀ (q : Fin n → Bool) (t : Space n),
      g (binaryAngularFundamentalBase q + t) = g t) :
    (∫ t : Space n,
      (κ t : ℂ) * g t
      ∂(volume : Measure (Space n))) = 0 := by sorry
