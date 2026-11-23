-- Prove2me | Theorems.Thm_ConcatFin_union_distrib
-- name    : ConcatFin_union_distrib
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:24:36.95954+00:00
-- url     : https://prove2.me/theorems/84eb13c3-c9f0-477e-a9d3-ebe679bc3a18
-- title:
--   Concat Fin union distrib: Concat Fin union distrib
-- statement:
--   The Concat Fin union distrib construction uses the Concat Fin union distrib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L114-L122
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L114-L122

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem ConcatFin_union_distrib {L0 L1 L2 : Set (List A)} :
    L0 * (L1 ∪ L2) = L0 * L1 ∪ L0 * L2 := by sorry
