-- Prove2me | Theorems.Thm_BooleanIsoperimetry_pairedCompression_reaches_canonical
-- name    : BooleanIsoperimetry.pairedCompression_reaches_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:49.59232+00:00
-- url     : https://prove2.me/theorems/8427f9e3-2d5c-42ca-bec3-40d93be207d3
-- title:
--   Boolean Isoperimetry: paired Compression reaches canonical
-- statement:
--   **Frankl–Füredi terminalization theorem.**
--
--   For any two slice families `(A, B)` there is *the* canonical cascade pair
--   `(A', B')` of the same total volume `|A| + |B|` with two-slice boundary cost no
--   larger than that of `(A, B)`.  This is the genuine set-family heart of the
--   Frankl–Füredi proof of Harper's theorem, stated as an existence/termination
--   statement so that the downstream scalar Macaulay leaves are *corollaries* of it
--   rather than the root of the development.
--
--   It is now assembled (sorry-free at this level) from the two PDF phases:
--
--   * `compress_to_simplicial_pair` — compress the arbitrary slices to simplicial
--     initial segments of their own sizes (dimension-`N` single-family Harper);
--   * `cascade_split_reaches_canonical` — compress the resulting sphere pair across the
--     top coordinate to the canonical cascade split (Kruskal–Katona/Macaulay).
--
--   Everything Harper-facing (`franklFuredi_pairedCompression_exchange`,
--   `H_exchange_max_form_pos`, `H_shadow_LE_sum` / `H_shadow_GT_sum`, the scalar leaves
--   `macaulay_extremal_pos_step_LE/GT`, `harper_macaulay_min`,
--   `harper_compression_descent`, `harper_vertex_iso`) is a sorry-free consequence of
--   these two phases.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2578-L2587
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2578-L2587

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

theorem BooleanIsoperimetry.pairedCompression_reaches_canonical {N : ℕ} (A B : Finset (Cube N)) :
    ∃ A' B' : Finset (Cube N), IsCanonicalCascadePair A' B' ∧
      A'.card + B'.card = A.card + B.card ∧
      PairShadowCost N A' B' ≤ PairShadowCost N A B := by sorry
