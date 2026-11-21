-- Prove2me | Theorems.Thm_Champernowne_getElemOption_bigDigits
-- name    : Champernowne.getElemOption_bigDigits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:15.437614+00:00
-- url     : https://prove2.me/theorems/2847e9c7-8c93-4268-ab90-1e70b8d38829
-- title:
--   Champernowne: get Elem Option big Digits
-- statement:
--   Big-endian digit extraction: position `j` of an `m`-digit number `n` is
--   `n / b^(m-1-j) % b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L325-L335
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L325-L335

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.getElemOption_bigDigits {b m n : ℕ} (hb : 1 < b)
    (hlen : (bigDigits b n).length = m) {j : ℕ} (hj : j < m) :
    (bigDigits b n)[j]? = some (n / b ^ (m - 1 - j) % b) := by sorry
