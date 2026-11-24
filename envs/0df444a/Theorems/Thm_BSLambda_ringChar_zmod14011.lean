-- Prove2me | Theorems.Thm_BSLambda_ringChar_zmod14011
-- name    : BSLambda.ringChar_zmod14011
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:42.631167+00:00
-- url     : https://prove2.me/theorems/272a2a9a-f822-47ae-b65d-01a01174ad65
-- title:
--   BSLambda: ring Char zmod14011
-- statement:
--   The characteristic of `F_14011` is not `2`. (Section 2 of `bs_lambda.txt`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L211-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L211-L213

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

theorem BSLambda.ringChar_zmod14011 : ringChar (ZMod 14011) ≠ 2 := by sorry
