-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_liftRaw_eq_any
-- name    : Auto.aux_CuboidNorm.eLpNorm_liftRaw_eq_any
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:47:59.470234+00:00
-- url     : https://prove2.me/theorems/dde83cc1-4e74-42ee-ba1c-ca39e3bc54a4
-- title:
--   aux Cuboid Norm: e Lp Norm lift Raw eq any
-- statement:
--   The coordinate `WithLp` equivalence preserves `eLpNorm` without an
--   additional measurability assumption.  This form is useful for jump
--   functions, whose measurability is not part of the real-variable hypothesis.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1653-L1668
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1653-L1668

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
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.eLpNorm_liftRaw_eq_any {n : ℕ} (F : RVector n → ℝ)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (aux_liftRaw F) p volume = eLpNorm F p volume := by sorry
