-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_exchange_q_zero
-- name    : BooleanIsoperimetry.H_exchange_q_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:06.501796+00:00
-- url     : https://prove2.me/theorems/9ba6a4b7-b1cd-4474-9ab0-9174f96d8f64
-- title:
--   Boolean Isoperimetry: H exchange q zero
-- statement:
--   **Degenerate (`q = 0`) regime of the cross-slice exchange — proved by pure
--   cascade arithmetic, no Kruskal–Katona needed.**  When the canonical cascade split
--   of `a + b` puts the whole mass in one slice (`q = 0`, hence `p = a + b`), the
--   canonical cross-boundary cost `H N p + p` is already at most the arbitrary-split
--   functional.  The cascade arithmetic lives upstream in
--   `Macaulay.harper_bc_min_q_zero_core` (it depends only on
--   `Cube`/`Cascade`/`Macaulay`); this restatement discharges the
--   degenerate regime of the Phase-2 leaf below.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2243-L2248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2243-L2248

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.H_exchange_q_zero {N a b p : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) (hp : p ≤ 2 ^ N)
    (hb_le_a : b ≤ a)
    (hpq : p = a + b) (hcasc : CascadeSplit N (a + b) p 0) :
    H N p + p ≤ max (H N a) b + max (H N b) a := by sorry
