-- Prove2me | Theorems.Thm_BooleanIsoperimetry_slice0_union
-- name    : BooleanIsoperimetry.slice0_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:46.146799+00:00
-- url     : https://prove2.me/theorems/b3bfd99b-102a-47cf-a81c-d7fb701afba2
-- title:
--   Boolean Isoperimetry: slice0 union
-- statement:
--   **The genuine Kruskal–Katona vertex-boundary upper-tail leaf (set-family form).**
--
--   This is the honest Frankl–Füredi/Macaulay content of `cascade_KK_tail_min`, stated
--   directly on Boolean-cube set families, Hamming layers, and unit neighborhoods —
--   no `ℤ`, no window bookkeeping, no scalar `H` arithmetic.  For a canonical cascade
--   split `(p, q)` of `a + b` that Macaulay-interleaves the arbitrary split `(a, b)`,
--   the number of high-Hamming-layer (`card ≥ k`) vertices in the two cross-slice
--   neighborhood unions of `(p, q)` is no larger than that of `(a, b)`:
--   `|{z ∈ N(IS p) ∪ IS q : |z| ≥ k}| + |{z ∈ N(IS q) ∪ IS p : |z| ≥ k}|`
--   `≤ |{z ∈ N(IS a) ∪ IS b : |z| ≥ k}| + |{z ∈ N(IS b) ∪ IS a : |z| ≥ k}|`,
--   where `IS m := simplicialInitSeg N m`.
--
--   At `k = 0` this is Harper's vertex-boundary recursion (`neighborhood_succ` gives
--   `|N(IS p) ∪ IS q| + |N(IS q) ∪ IS p| = H (N+1) (a+b)`); for `k ≥ 1` it is the
--   same comparison restricted to the upper Hamming layers, the Macaulay grid tail.
--   The faithful proof is the dimension recursion on `N` (`H_succ_slice` /
--   `neighborhood_succ`): slicing at the top coordinate reduces the level-`N`
--   upper-tail count with cutoff `k` to the level-`(N-1)` counts of the two slices
--   with cutoffs `k` (slice 0) and `k - 1` (slice 1), and the interleaving
--   majorization is inherited by the slice sub-splits via `CascadeInterleaves.lower_succ`.
--   This is the exact `dimension recursion + single-layer KK` route requested by the
--   Frankl–Füredi PDF, not a scalar reduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2412-L2415
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2412-L2415

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

theorem BooleanIsoperimetry.slice0_union {N : ℕ} (A B : Finset (Cube (N + 1))) :
    slice0 (A ∪ B) = slice0 A ∪ slice0 B := by sorry
