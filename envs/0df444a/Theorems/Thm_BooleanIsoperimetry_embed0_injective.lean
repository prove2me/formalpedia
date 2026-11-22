-- Prove2me | Theorems.Thm_BooleanIsoperimetry_embed0_injective
-- name    : BooleanIsoperimetry.embed0_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:14.689039+00:00
-- url     : https://prove2.me/theorems/67e86410-c649-426b-aca7-422f11801eee
-- title:
--   Boolean Isoperimetry: embed0 injective
-- statement:
--   `embed0` is injective: it is `Finset.image` along the injective `Fin.castSucc`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L165-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L165-L166

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

theorem BooleanIsoperimetry.embed0_injective {n : ℕ} : Function.Injective (@embed0 n) := by sorry
