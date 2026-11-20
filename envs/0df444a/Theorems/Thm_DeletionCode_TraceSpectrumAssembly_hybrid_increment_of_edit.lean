-- Prove2me | Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_increment_of_edit
-- name    : DeletionCode.TraceSpectrumAssembly.hybrid_increment_of_edit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:48:58.802718+00:00
-- url     : https://prove2.me/theorems/c1924a26-76e5-4e35-ab0a-f3b771fbf608
-- title:
--   Trace Spectrum Assembly: hybrid increment of edit
-- statement:
--   A separated edit's hybrid increment equals its actual isolated edit
--   on the original source. The common suffix is derived from the trace.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L62-L91
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L62-L91

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators

theorem DeletionCode.TraceSpectrumAssembly.hybrid_increment_of_edit {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (c : EditColumn trace) (g : Gram L) :
    spectrum (hybrid trace (c.val.val + 1)) L g - spectrum (hybrid trace c.val.val) L g =
      spectrum (oneEditTarget trace c) L g - spectrum trace.source L g := by sorry
