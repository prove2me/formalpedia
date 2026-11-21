-- Prove2me | Theorems.Thm_Champernowne_le_countOccurrences_champPrefix
-- name    : Champernowne.le_countOccurrences_champPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:56.300905+00:00
-- url     : https://prove2.me/theorems/a251fdad-cb88-4ae2-a6aa-dfb2215ff8a0
-- title:
--   Champernowne: le count Occurrences champ Prefix
-- statement:
--   `champBlocks (champIndex n)` is a genuine prefix of `champPrefix n`, so
--   its occurrence count only ever undercounts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L87-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L87-L93

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.le_countOccurrences_champPrefix (b n : ℕ) {w : List ℕ} (hwne : w ≠ []) :
    countOccurrences w (champBlocks b (champIndex b n))
      ≤ countOccurrences w (champPrefix b n) := by sorry
