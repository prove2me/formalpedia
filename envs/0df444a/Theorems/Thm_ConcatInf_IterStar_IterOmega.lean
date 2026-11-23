-- Prove2me | Theorems.Thm_ConcatInf_IterStar_IterOmega
-- name    : ConcatInf_IterStar_IterOmega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:24:57.148135+00:00
-- url     : https://prove2.me/theorems/f2421cf2-1a2b-43d9-bfff-cd2876e5ca99
-- title:
--   Concat Inf Iter Star Iter Omega: Concat Inf Iter Star Iter Omega
-- statement:
--   The Concat Inf Iter Star Iter Omega construction uses the Concat Inf Iter Star Iter Omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L256-L273
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L256-L273

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem ConcatInf_IterStar_IterOmega {L : Set (List A)} :
    L∗ * L^ω = L^ω := by sorry
