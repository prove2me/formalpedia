-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_split_min
-- name    : BooleanIsoperimetry.harper_split_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:09.009958+00:00
-- url     : https://prove2.me/theorems/3247cd4b-8d20-4c63-ac9d-9e5def9bd9e9
-- title:
--   Boolean Isoperimetry: harper split min
-- statement:
--   **Scalar Frankl–Füredi / Macaulay crux (★).**  The single inductive step of
--   Harper's vertex-isoperimetric theorem: for capacity-bounded slice masses
--   `x, y ≤ 2^n`, the boundary of the canonical split of `x + y` at level `n+1` is at
--   most the cross-slice boundary functional `max (H n x) y + max (H n y) x`.
--
--   This is the genuine remaining obstruction — the Frankl–Füredi paired-compression /
--   Kruskal–Katona–Macaulay shadow comparison — now stated as a pure scalar
--   inequality in three naturals.  It is strictly narrower than the family-level
--   `harper_vertex_iso` below (which is *proved* from it via the slice induction),
--   and is equivalent (through `H_succ_cascade`) to the finite-checked max-form
--   exchange step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L313-L319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L313-L319

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.harper_split_min {n x y : ℕ} (hx : x ≤ 2 ^ n) (hy : y ≤ 2 ^ n) :
    H (n + 1) (x + y) ≤ max (H n x) y + max (H n y) x := by sorry
