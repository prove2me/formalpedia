-- Prove2me | Theorems.Thm_Egrs75_lowDigits_iff_lowDoubleDigits
-- name    : Egrs75.lowDigits_iff_lowDoubleDigits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:15.928481+00:00
-- url     : https://prove2.me/theorems/ffd0b78c-0fe8-4283-83fe-c8ca6b9b9467
-- title:
--   Egrs75: low Digits iff low Double Digits
-- statement:
--   `LowDigits` and #376's `LowDoubleDigits` coincide for odd primes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Defs.lean#L68-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Defs.lean#L68-L73

module
public import Definitions.Def_LeanPool_Egrs75_CentralBinomialDigits
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_Defs
set_option autoImplicit true
@[expose] public section
public section
open Egrs75
open Nat

theorem Egrs75.lowDigits_iff_lowDoubleDigits {p n : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) :
    LowDigits p n ↔ Egrs75.Erdos376.LowDoubleDigits p n := by sorry
