-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_compression_descent
-- name    : BooleanIsoperimetry.harper_compression_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:43.872014+00:00
-- url     : https://prove2.me/theorems/d4d8bf6c-8141-4ef5-98ec-f4fea4db69df
-- title:
--   Boolean Isoperimetry: harper compression descent
-- statement:
--   **Harper's vertex-isoperimetric theorem (family level, slice-induction form).**
--   The simplicial initial segment of a given size has the smallest closed unit
--   neighborhood among all families of that size: `|N(initSeg N |A|)| ≤ |N(A)|`.
--
--   The proof is the PDF Frankl–Füredi dimension recursion: split a family
--   `B ⊆ Cube (M+1)` into its two `M`-dimensional slices, use `neighborhood_succ`,
--   lower-bound each cross term by a maximum via the dimension-`M` induction
--   hypothesis, and invoke the scalar Macaulay minimization `harper_macaulay_min`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L199-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L199-L244

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

theorem BooleanIsoperimetry.harper_compression_descent {N : ℕ} (A : Finset (Cube N)) :
    (neighborhood 1 (simplicialInitSeg N A.card)).card ≤ (neighborhood 1 A).card := by sorry
