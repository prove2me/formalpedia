-- Prove2me | Theorems.Thm_BooleanIsoperimetry_compression_embed0_injective
-- name    : BooleanIsoperimetry.compression_embed0_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:33.478461+00:00
-- url     : https://prove2.me/theorems/75055dab-8010-4a8d-9882-b1d06adbf421
-- title:
--   Boolean Isoperimetry: compression embed0 injective
-- statement:
--   `embed0` is injective.  Kept local to the paired-compression layer so the
--   embedded-pair slice lemmas do not depend on the later scalar bridge file.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L47-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L47-L48

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

theorem BooleanIsoperimetry.compression_embed0_injective {N : ℕ} : Function.Injective (@embed0 N) := by sorry
