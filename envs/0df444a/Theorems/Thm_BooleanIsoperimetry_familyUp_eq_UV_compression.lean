-- Prove2me | Theorems.Thm_BooleanIsoperimetry_familyUp_eq_UV_compression
-- name    : BooleanIsoperimetry.familyUp_eq_UV_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:44.305816+00:00
-- url     : https://prove2.me/theorems/247c8a5b-47b4-45b2-ab2c-1892b46b3a6e
-- title:
--   Boolean Isoperimetry: family Up eq UV compression
-- statement:
--   **Block-move ↔ mathlib `UV`-compression dictionary.**  For disjoint blocks the
--   project's family `𝒰`-move is literally mathlib's `UV`-compression with the slots
--   swapped: `familyUp U V A = UV.compression V U A`.  Proved set-theoretically from
--   `compress_VU_eq_blockReplace`, identifying the image form (`familyUpMap`, which
--   keeps a set fixed when its replacement already lies in `A`) with mathlib's
--   "stay / move" split (`UV.mem_compression`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L773-L810
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L773-L810

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

theorem BooleanIsoperimetry.familyUp_eq_UV_compression {N : ℕ} (A : Finset (Cube N)) {U V : Cube N}
    (hd : Disjoint U V) :
    familyUp U V A = UV.compression V U A := by sorry
