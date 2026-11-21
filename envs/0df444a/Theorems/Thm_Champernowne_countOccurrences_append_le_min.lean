-- Prove2me | Theorems.Thm_Champernowne_countOccurrences_append_le_min
-- name    : Champernowne.countOccurrences_append_le_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:27.981171+00:00
-- url     : https://prove2.me/theorems/bb47fef2-b6ea-4178-b801-eb7f48317dd7
-- title:
--   Champernowne: count Occurrences append le min
-- statement:
--   Append sandwich, upper bound: at most `min w.length a.length`
--   occurrences straddle the seam (they must start within `w.length − 1`
--   slots of the end of `a`, and there are only `a.length` interior start
--   slots).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L62-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L62-L93

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.countOccurrences_append_le_min (w a b : List ℕ) :
    countOccurrences w (a ++ b)
      ≤ countOccurrences w a + countOccurrences w b
        + min w.length a.length := by sorry
