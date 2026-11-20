-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_spectrum_nonzero_iff_occurs
-- name    : DeletionCode.SpectrumPath.spectrum_nonzero_iff_occurs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:22:10.326401+00:00
-- url     : https://prove2.me/theorems/083d6fbe-ec8e-452c-93a5-72c24ebc9c88
-- title:
--   Spectrum Path: spectrum nonzero iff occurs
-- statement:
--   The Spectrum Path construction uses the spectrum nonzero iff occurs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L41-L46
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L41-L46

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.spectrum_nonzero_iff_occurs (word : Letters) (n L : ℕ) (g : Gram L) :
    wordSpectrum word n L g ≠ 0 ↔ ∃ a, a + L ≤ n ∧ gram word L a = g := by sorry
