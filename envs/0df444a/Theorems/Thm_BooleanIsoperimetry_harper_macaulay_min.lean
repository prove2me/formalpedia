-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_macaulay_min
-- name    : BooleanIsoperimetry.harper_macaulay_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:33.087728+00:00
-- url     : https://prove2.me/theorems/f74a90cb-2f60-48b9-b13e-c26a75cc7246
-- title:
--   Boolean Isoperimetry: harper macaulay min
-- statement:
--   **Scalar Macaulay minimization — the arithmetic core of Harper.**
--   For any slice sizes `a, b ≤ 2 ^ N`, the boundary cost `H (N+1) (a+b)` of the
--   canonical cascade split of the total mass `a + b` is minimal among all ways of
--   distributing that mass into two `N`-dimensional slices of sizes `a` and `b`.
--
--   Proved by strong induction on the dimension `N` (the Frankl–Füredi recursion):
--   `H_succ_cascade` reduces the LHS to `max (H N p) q + max (H N q) p`, and
--   `macaulay_bc_min` closes it using the lower-dimensional induction hypothesis.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L162-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L162-L176

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

theorem BooleanIsoperimetry.harper_macaulay_min {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    H (N + 1) (a + b) ≤ max (H N a) b + max (H N b) a := by sorry
