-- Prove2me | Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_zero
-- name    : DeletionCode.TraceSpectrumAssembly.hybrid_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:49:07.191182+00:00
-- url     : https://prove2.me/theorems/c16e86c0-2e32-4689-8e82-be852220d2d5
-- title:
--   Trace Spectrum Assembly: hybrid zero
-- statement:
--   The Trace Spectrum Assembly construction uses the hybrid zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L23-L24
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L23-L24

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators

theorem DeletionCode.TraceSpectrumAssembly.hybrid_zero (trace : Trace) : hybrid trace 0 = trace.source := by sorry
