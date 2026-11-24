-- Prove2me | Theorems.Thm_FockSPR_safe_square
-- name    : FockSPR.safe_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:41.140133+00:00
-- url     : https://prove2.me/theorems/e24d7b96-881f-4898-a1a5-3e94f9a44878
-- title:
--   Fock SPR: safe square
-- statement:
--   The Fock SPR construction uses the safe square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/SafeSquare.lean#L39-L40
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/SafeSquare.lean#L39-L40

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

theorem FockSPR.safe_square (a b : ℝ) : (a + b) ^ 2 ≥ (1 / 2) * a ^ 2 - b ^ 2 := by sorry
