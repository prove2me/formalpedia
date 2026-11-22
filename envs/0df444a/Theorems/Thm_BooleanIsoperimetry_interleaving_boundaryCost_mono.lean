-- Prove2me | Theorems.Thm_BooleanIsoperimetry_interleaving_boundaryCost_mono
-- name    : BooleanIsoperimetry.interleaving_boundaryCost_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:51.676595+00:00
-- url     : https://prove2.me/theorems/4ea29ce0-5908-46ee-8c8e-a335d1762ab2
-- title:
--   Boolean Isoperimetry: interleaving boundary Cost mono
-- statement:
--   Macaulay interleaving theorem: if `(p, q)` interleaves `(a, b)`, then its
--   boundary cost is smaller.  Through the cascade recursion `H_succ_cascade` this
--   reduces to Harper's recursion inequality `harper_core`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2047-L2055
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2047-L2055

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.interleaving_boundaryCost_mono
    {n p q a b : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (h_inter : CascadeInterleaves n p q a b) :
    boundaryCost n p q ≤ boundaryCost n a b := by sorry
