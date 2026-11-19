-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_spectrum_at_occurrence_positive
-- name    : DeletionCode.SpectrumPath.spectrum_at_occurrence_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:11:15.244382+00:00
-- url     : https://prove2.me/theorems/b213fbf8-ae8a-4612-8e91-d560d3b8e089
-- title:
--   Spectrum Path: spectrum at occurrence positive
-- statement:
--   The Spectrum Path construction uses the spectrum at occurrence positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L23-L39
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L23-L39

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.spectrum_at_occurrence_positive (word : Letters) (n L a : ℕ) (g : Gram L)
    (ha : a + L ≤ n) (hg : gram word L a = g) :
    0 < wordSpectrum word n L g := by sorry
