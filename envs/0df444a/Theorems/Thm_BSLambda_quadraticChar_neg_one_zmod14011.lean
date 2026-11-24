-- Prove2me | Theorems.Thm_BSLambda_quadraticChar_neg_one_zmod14011
-- name    : BSLambda.quadraticChar_neg_one_zmod14011
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:43.895622+00:00
-- url     : https://prove2.me/theorems/abb2827e-32a9-4b87-bc06-d37f3d768108
-- title:
--   BSLambda: quadratic Char neg one zmod14011
-- statement:
--   Since `14011 ≡ 3 mod 4`, the element `-1` is a nonresidue in `F_14011`; this is what makes
--   the Paley orientation a tournament. (Section 2 of `bs_lambda.txt`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L217-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L217-L219

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
set_option autoImplicit true
@[expose] public section
public section
open Finset
open BSLambda

theorem BSLambda.quadraticChar_neg_one_zmod14011 : quadraticChar (ZMod 14011) (-1) = -1 := by sorry
