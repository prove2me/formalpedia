-- Prove2me | Theorems.Thm_BSLambda_paley_isDR
-- name    : BSLambda.paley_isDR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:43.499166+00:00
-- url     : https://prove2.me/theorems/966b7615-a232-49cc-96c9-373ba70fed06
-- title:
--   BSLambda: paley is DR
-- statement:
--   **The Paley tournament on `F_14011` is doubly regular** with `d = 7005` and `t = 3502`.
--   (Section 2 of `bs_lambda.txt`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L272-L273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L272-L273

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

theorem BSLambda.paley_isDR : IsDRTournamentWith (paleyArc 14011) 7005 3502 := by sorry
