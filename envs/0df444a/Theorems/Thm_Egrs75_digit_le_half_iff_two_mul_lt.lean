-- Prove2me | Theorems.Thm_Egrs75_digit_le_half_iff_two_mul_lt
-- name    : Egrs75.digit_le_half_iff_two_mul_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:17.409879+00:00
-- url     : https://prove2.me/theorems/5de48534-1a4d-4ccd-ba89-e1cf08e36534
-- title:
--   Egrs75: digit le half iff two mul lt
-- statement:
--   For an **odd** prime `p`, the per-digit bound `2*d < p` (the #376 form, i.e.
--   "doubling produces no carry") is equivalent to `d ≤ (p-1)/2` (the `LowDigits`
--   form). The hypotheses are stated per-digit so the lemma threads through the
--   `∀ d ∈ digits p n` quantifier.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Defs.lean#L57-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Defs.lean#L57-L65

module
public import Definitions.Def_LeanPool_Egrs75_CentralBinomialDigits
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_Defs
set_option autoImplicit true
@[expose] public section
public section
open Egrs75
open Nat

theorem Egrs75.digit_le_half_iff_two_mul_lt {p d : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) :
    d ≤ (p - 1) / 2 ↔ 2 * d < p := by sorry
