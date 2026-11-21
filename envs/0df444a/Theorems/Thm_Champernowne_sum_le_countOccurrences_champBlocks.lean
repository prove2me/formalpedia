-- Prove2me | Theorems.Thm_Champernowne_sum_le_countOccurrences_champBlocks
-- name    : Champernowne.sum_le_countOccurrences_champBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:16.769122+00:00
-- url     : https://prove2.me/theorems/8d429429-d671-464c-87d0-42494871d26a
-- title:
--   Champernowne: sum le count Occurrences champ Blocks
-- statement:
--   Per-number occurrences survive in the stream.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L75-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L75-L88

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.sum_le_countOccurrences_champBlocks {b : ℕ} {w : List ℕ}
    (hw : w ≠ []) (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 (N + 1), countOccurrences w (bigDigits b n)
      ≤ countOccurrences w (champBlocks b N) := by sorry
