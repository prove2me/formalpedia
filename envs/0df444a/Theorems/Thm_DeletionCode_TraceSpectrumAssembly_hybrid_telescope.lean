-- Prove2me | Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_telescope
-- name    : DeletionCode.TraceSpectrumAssembly.hybrid_telescope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:49:09.778181+00:00
-- url     : https://prove2.me/theorems/6f79b84e-ae14-456b-898f-9e2ccefa1dbf
-- title:
--   Trace Spectrum Assembly: hybrid telescope
-- statement:
--   Exact telescoping over every actual column; no separation is needed yet.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L94-L101
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L94-L101

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators

theorem DeletionCode.TraceSpectrumAssembly.hybrid_telescope (trace : Trace) (L : ℕ) (g : Gram L) :
    spectrum trace.target L g - spectrum trace.source L g =
      ∑ i : Fin trace.length,
        (spectrum (hybrid trace (i.val + 1)) L g - spectrum (hybrid trace i.val) L g) := by sorry
