-- Prove2me | Theorems.Thm_Ehrhart_JetAsymptotics_tendsto_shifted_floor_mul_div_nat
-- name    : Ehrhart.JetAsymptotics.tendsto_shifted_floor_mul_div_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/1ff229e4-32aa-49a4-a63a-cad8aa7c88ba
-- title:
--   Ehrhart.JetAsymptotics.tendsto_shifted_floor_mul_div_nat
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
open Ehrhart.JetAsymptotics
open Asymptotics Filter MeasureTheory
open scoped BigOperators Topology

theorem Ehrhart.JetAsymptotics.tendsto_shifted_floor_mul_div_nat
    {t : ℝ} (ht : 0 ≤ t) (b : ℕ) :
    Tendsto
      (fun k : ℕ =>
        ((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) / (k : ℝ))
      atTop (𝓝 t) := by sorry
