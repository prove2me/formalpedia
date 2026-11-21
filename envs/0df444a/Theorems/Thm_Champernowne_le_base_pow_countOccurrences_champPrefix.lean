-- Prove2me | Theorems.Thm_Champernowne_le_base_pow_countOccurrences_champPrefix
-- name    : Champernowne.le_base_pow_countOccurrences_champPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:55.927176+00:00
-- url     : https://prove2.me/theorems/e6fa0b01-ea6e-4815-8e5c-1b4689e2c9be
-- title:
--   Champernowne: le base pow count Occurrences champ Prefix
-- statement:
--   Main transfer, lower: for `b^(M-1) ≤ champIndex b n + 1 ≤ b^M` and
--   `w.length ≤ M`, `n ≤ b^k · countOccurrences w (champPrefix b n) +
--   7(k+1)·b^k·b^M`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L98-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L98-L136

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.le_base_pow_countOccurrences_champPrefix {b : ℕ} (hb : 1 < b) (n M : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hM : 0 < M) (hwM : w.length ≤ M)
    (h1 : b ^ (M - 1) ≤ champIndex b n + 1) (h2 : champIndex b n + 1 ≤ b ^ M) :
    n ≤ b ^ w.length * countOccurrences w (champPrefix b n)
      + 7 * (w.length + 1) * b ^ w.length * b ^ M := by sorry
