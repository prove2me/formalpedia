-- Prove2me | Theorems.Thm_BooleanIsoperimetry_embed1_injective
-- name    : BooleanIsoperimetry.embed1_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:17.163004+00:00
-- url     : https://prove2.me/theorems/d9105c06-978c-4fcd-b00b-29426bb5cfc2
-- title:
--   Boolean Isoperimetry: embed1 injective
-- statement:
--   `embed1` is injective: it inserts the top coordinate into the image of the
--   injective `Fin.castSucc`, and that top coordinate is never already present.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L170-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L170-L176

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

theorem BooleanIsoperimetry.embed1_injective {n : ℕ} : Function.Injective (@embed1 n) := by sorry
