-- Prove2me | Theorems.Thm_Champernowne_base_pow_countOccurrences_champPrefix_le
-- name    : Champernowne.base_pow_countOccurrences_champPrefix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:57.023425+00:00
-- url     : https://prove2.me/theorems/15179ab1-ef54-4605-928b-4bdac76de298
-- title:
--   Champernowne: base pow count Occurrences champ Prefix le
-- statement:
--   Main transfer, upper — derived from the lower transfer by complement:
--   a window position matches exactly one of the `b^k` length-`k` words, so
--   `b^k·(occ w + Σ_{v ≠ w} occ v) ≤ b^k·(n+1)` (`sum_countOccurrences_allWords_le`),
--   while the lower transfer applied to each of the `b^k − 1` words `v ≠ w`
--   bounds `Σ_{v ≠ w} b^k·occ v` from below. Costs one extra `b^k` factor in
--   the error over the lower bound's `7(k+1)·b^k·b^M`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L144-L197
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L144-L197

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.base_pow_countOccurrences_champPrefix_le {b : ℕ} (hb : 1 < b) (n M : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hM : 0 < M) (hwM : w.length ≤ M)
    (h1 : b ^ (M - 1) ≤ champIndex b n + 1) (h2 : champIndex b n + 1 ≤ b ^ M) :
    b ^ w.length * countOccurrences w (champPrefix b n)
      ≤ n + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ M := by sorry
