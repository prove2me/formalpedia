-- Prove2me | Theorems.Thm_BooleanIsoperimetry_last_not_mem_image_castSucc
-- name    : BooleanIsoperimetry.last_not_mem_image_castSucc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:21.790255+00:00
-- url     : https://prove2.me/theorems/299a3d9f-df2c-4629-aad3-c599db2d48ea
-- title:
--   Boolean Isoperimetry: last not mem image cast Succ
-- statement:
--   The top coordinate `Fin.last n` never lies in the image of `Fin.castSucc`,
--   since `Fin.castSucc i < Fin.last n` always.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L158-L162
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L158-L162

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

theorem BooleanIsoperimetry.last_not_mem_image_castSucc {n : ℕ} (x : Cube n) :
    Fin.last n ∉ x.image Fin.castSucc := by sorry
