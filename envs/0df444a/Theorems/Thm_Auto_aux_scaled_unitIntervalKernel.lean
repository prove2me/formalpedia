-- Prove2me | Theorems.Thm_Auto_aux_scaled_unitIntervalKernel
-- name    : Auto.aux_scaled_unitIntervalKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:05.178822+00:00
-- url     : https://prove2.me/theorems/b3f405c3-450a-4414-8422-9f3f466a808d
-- title:
--   Auto: aux scaled unit Interval Kernel
-- statement:
--   Rescaling the half-open unit-interval kernel by a positive integer gives
--   the indicator of the corresponding half-open scale interval.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L345-L371
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L345-L371

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_scaled_unitIntervalKernel {N : ℕ} (hN : 0 < N) (s : ℝ) :
    (N : ℝ)⁻¹ * ctUnitIntervalKernel ((N : ℝ)⁻¹ * s) =
      (N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator (fun _ ↦ (1 : ℝ)) s := by sorry
