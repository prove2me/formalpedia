-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_spectrum_at_occurrence_one
-- name    : DeletionCode.SpectrumPath.spectrum_at_occurrence_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:22:25.856526+00:00
-- url     : https://prove2.me/theorems/e82119ee-0527-4561-9de7-63262b68a219
-- title:
--   Spectrum Path: spectrum at occurrence one
-- statement:
--   The Spectrum Path construction uses the spectrum at occurrence one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L57-L74
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L57-L74

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.spectrum_at_occurrence_one (word : Letters) (n L a : ℕ) (g : Gram L)
    (hunique : KUnique word n (L - 1))
    (ha : a + L ≤ n) (hg : gram word L a = g) :
    wordSpectrum word n L g = 1 := by sorry
