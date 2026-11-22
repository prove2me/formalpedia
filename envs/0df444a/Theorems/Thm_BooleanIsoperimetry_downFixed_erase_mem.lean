-- Prove2me | Theorems.Thm_BooleanIsoperimetry_downFixed_erase_mem
-- name    : BooleanIsoperimetry.downFixed_erase_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:12.020807+00:00
-- url     : https://prove2.me/theorems/2ffbc8b2-5278-4e10-bd79-1c04d3b72fbe
-- title:
--   Boolean Isoperimetry: down Fixed erase mem
-- statement:
--   A coordinate-Down-fixed family is closed under deleting any present
--   coordinate: if `x ∈ A` and `i ∈ x` then `x.erase i ∈ A`.  This is the forward
--   direction of the `IsCoordinateDown i A A` fixed-point characterization.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1301-L1311
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1301-L1311

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

theorem BooleanIsoperimetry.downFixed_erase_mem {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) {x : Cube N} (hx : x ∈ A) {i : Fin N} (hi : i ∈ x) :
    x.erase i ∈ A := by sorry
