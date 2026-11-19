-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_equal_spectrum_recovers_word
-- name    : DeletionCode.SpectrumPath.equal_spectrum_recovers_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:11:14.450828+00:00
-- url     : https://prove2.me/theorems/7d0979f2-205e-4328-b6e5-4c8c8d982cc8
-- title:
--   Spectrum Path: equal spectrum recovers word
-- statement:
--   Equality of actual spectra recovers the finite word; no uniqueness of z is assumed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L123-L144
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L123-L144

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.equal_spectrum_recovers_word (word z : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1))
    (hspectrum : wordSpectrum z n L = wordSpectrum word n L) :
    Agree z 0 word 0 n := by sorry
