-- Prove2me | Theorems.Thm_DeletionCode_TraceMatchedSuffix_matchedAnchor_gap_le
-- name    : DeletionCode.TraceMatchedSuffix.matchedAnchor_gap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:41:36.070505+00:00
-- url     : https://prove2.me/theorems/73183eb9-49f9-461d-a0d6-d9932e667096
-- title:
--   Trace Matched Suffix: matched Anchor gap le
-- statement:
--   The Trace Matched Suffix construction uses the matched Anchor gap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L21-L30
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceMatchedSuffix.lean#L21-L30

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
set_option autoImplicit true
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation

theorem DeletionCode.TraceMatchedSuffix.matchedAnchor_gap_le (trace : Trace) (i j : ℕ) (hij : i ≤ j) :
    trace.matchedAnchor j ≤ trace.matchedAnchor i + (j - i) := by sorry
