-- Prove2me | Theorems.Thm_BooleanIsoperimetry_downFixed_sdiff_mem
-- name    : BooleanIsoperimetry.downFixed_sdiff_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:57.004154+00:00
-- url     : https://prove2.me/theorems/ef4bd439-3526-41ec-8714-c30cf43cc60f
-- title:
--   Boolean Isoperimetry: down Fixed sdiff mem
-- statement:
--   Iterating `downFixed_erase_mem`: a coordinate-Down-fixed family is closed
--   under removing any sub-block `W ⊆ S`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1315-L1334
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1315-L1334

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

theorem BooleanIsoperimetry.downFixed_sdiff_mem {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) {S W : Cube N} (hS : S ∈ A) (hWS : W ⊆ S) :
    S \ W ∈ A := by sorry
