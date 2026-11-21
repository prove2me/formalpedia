-- Prove2me | Theorems.Thm_Champernowne_add_countOccurrences_le_append
-- name    : Champernowne.add_countOccurrences_le_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:34:49.280967+00:00
-- url     : https://prove2.me/theorems/0f106494-9a66-43ba-adc9-08011fabdb7e
-- title:
--   Champernowne: add count Occurrences le append
-- statement:
--   Lower bound: occurrences inside `a` and inside `b` survive in `a ++ b`.
--   Fails for `w = []` (window counts overlap at the seam).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L54-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L54-L70

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

theorem Champernowne.add_countOccurrences_le_append {w : List ℕ} (hw : w ≠ [])
    (a b : List ℕ) :
    countOccurrences w a + countOccurrences w b
      ≤ countOccurrences w (a ++ b) := by sorry
