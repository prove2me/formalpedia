-- Prove2me | Theorems.Thm_DeletionCode_TraceSpectrumAssembly_spectrum_sum_apply
-- name    : DeletionCode.TraceSpectrumAssembly.spectrum_sum_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:49:13.328549+00:00
-- url     : https://prove2.me/theorems/835ea7a6-0c24-4319-89e7-22195ba8567c
-- title:
--   Trace Spectrum Assembly: spectrum sum apply
-- statement:
--   The full trace's spectrum difference is the sum of isolated edit
--   differences, indexed by its actual deletion and insertion columns.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L105-L131
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L105-L131

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators

theorem DeletionCode.TraceSpectrumAssembly.spectrum_sum_apply {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (g : Gram L) :
    spectrum trace.target L g - spectrum trace.source L g =
      ∑ c : EditColumn trace,
        (spectrum (oneEditTarget trace c) L g - spectrum trace.source L g) := by sorry
