-- Prove2me | Theorems.Thm_DeletionCode_TraceSpectrumAssembly_spectrum_sum
-- name    : DeletionCode.TraceSpectrumAssembly.spectrum_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:49:17.287171+00:00
-- url     : https://prove2.me/theorems/14cf70ce-f9d2-4f31-8d56-f23b6cac1903
-- title:
--   Trace Spectrum Assembly: spectrum sum
-- statement:
--   The actual signed integer vector identity used to assemble the
--   separated-edit catalogue. No uniqueness or spectrum-sum premise is required.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L135-L145
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean#L135-L145

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators

theorem DeletionCode.TraceSpectrumAssembly.spectrum_sum {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) :
    wordSpectrum (CatalogueWords.listLetters trace.target) trace.target.length L -
      wordSpectrum (CatalogueWords.listLetters trace.source) trace.source.length L =
      ∑ c : EditColumn trace,
        (wordSpectrum (CatalogueWords.listLetters (oneEditTarget trace c))
            (oneEditTarget trace c).length L -
          wordSpectrum (CatalogueWords.listLetters trace.source) trace.source.length L) := by sorry
