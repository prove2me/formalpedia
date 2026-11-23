-- Prove2me | Theorems.Thm_ConcatInf_mono
-- name    : ConcatInf_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:24:40.283517+00:00
-- url     : https://prove2.me/theorems/5b095170-75ef-43a7-b1d2-d9d1eac9bea3
-- title:
--   Concat Inf mono: Concat Inf mono
-- statement:
--   The Concat Inf mono construction uses the Concat Inf mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L146-L150
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L146-L150

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem ConcatInf_mono {L0 L0' : Set (List A)} {L1 L1' : Set (Stream' A)}
    (h0 : L0 ⊆ L0') (h1 : L1 ⊆ L1') :
    L0 * L1 ⊆ L0' * L1' := by sorry
