-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_core
-- name    : BooleanIsoperimetry.harper_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:45.939958+00:00
-- url     : https://prove2.me/theorems/4b84daa3-614f-43a9-b263-0ce31d3f3603
-- title:
--   Boolean Isoperimetry: harper core
-- statement:
--   Harper's vertex-isoperimetric recursion inequality (the genuine combinatorial
--   core): the initial segment of size `a + b` in the `(n+1)`-cube has the smallest
--   closed `1`-neighborhood among all sets obtained by taking initial segments of
--   sizes `a`, `b` in the two slices.  Equivalently, in `H`-terms,
--   `H (n+1) (a+b) ≤ max (H n a) b + max (H n b) a`.
--
--   This is proved independently of `boundaryCost`, `CascadeInterleaves`,
--   `H_inequality_core`, `H_inequality`, `macaulay_optimization`, and
--   `interleaving_boundaryCost_mono` (all of which are stated later and ultimately
--   depend on this lemma), so there is no circularity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2020-L2032
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2020-L2032

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

theorem BooleanIsoperimetry.harper_core :
    ∀ (n a b : ℕ), a ≤ 2 ^ n → b ≤ 2 ^ n →
      H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a := by sorry
