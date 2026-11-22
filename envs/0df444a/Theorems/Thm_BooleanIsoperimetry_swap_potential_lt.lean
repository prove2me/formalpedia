-- Prove2me | Theorems.Thm_BooleanIsoperimetry_swap_potential_lt
-- name    : BooleanIsoperimetry.swap_potential_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:43.885697+00:00
-- url     : https://prove2.me/theorems/f713d52d-cc04-4493-9135-57161c0e9f0c
-- title:
--   Boolean Isoperimetry: swap potential lt
-- statement:
--   A rank-lowering single-set swap strictly decreases the rank potential
--   `compressionPotential = ∑ rank`: replacing `x` by an earlier set `y`
--   (`simplicialLt y x`, hence `rank y < rank x`) lowers the sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L539-L549
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L539-L549

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

theorem BooleanIsoperimetry.swap_potential_lt {N : ℕ} {A A' : Finset (Cube N)} {x y : Cube N}
    (hx : x ∈ A) (hy : y ∉ A) (hlt : simplicialLt y x)
    (heq : A' = insert y (A.erase x)) :
    compressionPotential A' < compressionPotential A := by sorry
