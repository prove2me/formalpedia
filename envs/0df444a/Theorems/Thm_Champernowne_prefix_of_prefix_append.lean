-- Prove2me | Theorems.Thm_Champernowne_prefix_of_prefix_append
-- name    : Champernowne.prefix_of_prefix_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:24.180796+00:00
-- url     : https://prove2.me/theorems/1687840c-5aa2-403f-bcc8-13953cb20282
-- title:
--   Champernowne: prefix of prefix append
-- statement:
--   A prefix short enough to fit inside `a` is a prefix of `a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L42-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L42-L51

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.prefix_of_prefix_append {α : Type*} {w a c : List α}
    (h : w <+: a ++ c) (hl : w.length ≤ a.length) : w <+: a := by sorry
