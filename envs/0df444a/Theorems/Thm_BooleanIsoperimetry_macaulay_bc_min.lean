-- Prove2me | Theorems.Thm_BooleanIsoperimetry_macaulay_bc_min
-- name    : BooleanIsoperimetry.macaulay_bc_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:04.03851+00:00
-- url     : https://prove2.me/theorems/1decb213-6548-4a6f-8754-1d88fd4a2f77
-- title:
--   Boolean Isoperimetry: macaulay bc min
-- statement:
--   **Scalar boundary-cost minimization at a fixed cascade split.**  Given the
--   canonical cascade split `(p, q)` of `a + b` at level `n`, the canonical split
--   minimizes the symmetric max-form boundary cost.  The `q = 0` branch is discharged
--   sorry-free by `Macaulay.harper_bc_min_q_zero_core`, and the `q ≥ 1` branch by
--   `macaulay_extremal_pos_step`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L129-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L129-L152

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_MacaulayMin
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.macaulay_bc_min (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by sorry
