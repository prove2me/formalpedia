-- Prove2me | Theorems.Thm_FockSPR_nonneg_safe_square
-- name    : FockSPR.nonneg_safe_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:05.076281+00:00
-- url     : https://prove2.me/theorems/0ef12c9d-3ca9-46cf-9de2-b1712c8820c4
-- title:
--   Fock SPR: nonneg safe square
-- statement:
--   The Fock SPR construction uses the nonneg safe square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/SafeSquare.lean#L54-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/SafeSquare.lean#L54-L58

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_SafeSquare
set_option autoImplicit true
@[expose] public section
public section
open Real
open FockSPR

theorem FockSPR.nonneg_safe_square (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a ≥ b - c) : a ^ 2 ≥ (1 / 2) * b ^ 2 - c ^ 2 := by sorry
