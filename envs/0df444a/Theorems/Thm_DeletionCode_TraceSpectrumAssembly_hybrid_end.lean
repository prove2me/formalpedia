-- Prove2me | Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_end
-- name    : DeletionCode.TraceSpectrumAssembly.hybrid_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:48:33.660172+00:00
-- url     : https://prove2.me/theorems/7434fd87-687a-4a74-a326-7af59ed1d3ae
-- title:
--   Trace Spectrum Assembly: hybrid end
-- statement:
--   The Trace Spectrum Assembly construction uses the hybrid end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L26-L27
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L26-L27

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators

theorem DeletionCode.TraceSpectrumAssembly.hybrid_end (trace : Trace) : hybrid trace trace.length = trace.target := by sorry
