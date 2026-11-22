-- Prove2me | Theorems.Thm_BooleanIsoperimetry_macaulay_extremal_pos_step
-- name    : BooleanIsoperimetry.macaulay_extremal_pos_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:00.276809+00:00
-- url     : https://prove2.me/theorems/754bc290-0682-4d3a-b175-be4175ee6a56
-- title:
--   Boolean Isoperimetry: macaulay extremal pos step
-- statement:
--   Positive-cascade max-form wrapper.  Sorry-free modulo the two oriented
--   Macaulay shadow-sum leaves `macaulay_extremal_pos_step_LE` and
--   `macaulay_extremal_pos_step_GT`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L95-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L95-L122

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

theorem BooleanIsoperimetry.macaulay_extremal_pos_step (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) (hq_pos : 1 ≤ q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by sorry
