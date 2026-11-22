-- Prove2me | Theorems.Thm_BooleanIsoperimetry_boundaryCost_le_of_interleaves_core
-- name    : BooleanIsoperimetry.boundaryCost_le_of_interleaves_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:14.46137+00:00
-- url     : https://prove2.me/theorems/f04fde4c-a2bd-49fa-9cef-8f058d3c9358
-- title:
--   Boolean Isoperimetry: boundary Cost le of interleaves core
-- statement:
--   Frankl-Füredi inductive boundary monotonicity for a cascade-interleaving profile.
--
--   This is the remaining local compression/Macaulay step in the form actually used
--   by the Harper induction: the arbitrary split has capacity bounds, and the proof
--   may use the already-established lower-dimensional Harper inequality.  The older
--   capacity-free, `ih`-free version was stronger than the live proof route and hid
--   the PDF's inductive input.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1171-L1185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1171-L1185

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

theorem BooleanIsoperimetry.boundaryCost_le_of_interleaves_core (n p q a b : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (h_inter : CascadeInterleaves (n + 1) p q a b) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by sorry
