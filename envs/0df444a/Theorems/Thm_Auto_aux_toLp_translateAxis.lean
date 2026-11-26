-- Prove2me | Theorems.Thm_Auto_aux_toLp_translateAxis
-- name    : Auto.aux_toLp_translateAxis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:33.903474+00:00
-- url     : https://prove2.me/theorems/4fbb6eb7-b58e-48f0-a396-70237a2718fc
-- title:
--   Auto: aux to Lp translate Axis
-- statement:
--   The raw-coordinate translation agrees with translation by
--   `ctCoordinateAxis` after passing to Euclidean space.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L618-L623
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L618-L623

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

theorem Auto.aux_toLp_translateAxis {n : ℕ} (x : aux_RVector n)
    (i : Fin n) (s : ℝ) :
    WithLp.toLp 2 (aux_translateAxis x i s) =
      WithLp.toLp 2 x + s • ctCoordinateAxis i := by sorry
