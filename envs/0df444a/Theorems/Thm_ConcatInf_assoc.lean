-- Prove2me | Theorems.Thm_ConcatInf_assoc
-- name    : ConcatInf_assoc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:34:09.415808+00:00
-- url     : https://prove2.me/theorems/5e24989f-be40-4d1a-8c3f-ab3d59efa852
-- title:
--   Concat Inf assoc: Concat Inf assoc
-- statement:
--   The Concat Inf assoc construction uses the Concat Inf assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L137-L144
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L137-L144

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem ConcatInf_assoc {L0 L0' : Set (List A)} {L1 : Set (Stream' A)} :
    (L0 * L0') * L1 = L0 * (L0' * L1) := by sorry
