-- Prove2me | Theorems.Thm_Champernowne_take_add_drop_countOccurrences_le
-- name    : Champernowne.take_add_drop_countOccurrences_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:17.684184+00:00
-- url     : https://prove2.me/theorems/302f3536-218f-421f-8dd9-4a502998cd93
-- title:
--   Champernowne: take add drop count Occurrences le
-- statement:
--   Cutting at `n` never gains occurrences (for `w ≠ []`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L162-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L162-L167

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.take_add_drop_countOccurrences_le {w : List ℕ} (hw : w ≠ [])
    (l : List ℕ) (n : ℕ) :
    countOccurrences w (l.take n) + countOccurrences w (l.drop n)
      ≤ countOccurrences w l := by sorry
