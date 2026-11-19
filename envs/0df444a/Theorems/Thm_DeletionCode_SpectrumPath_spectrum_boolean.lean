-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_spectrum_boolean
-- name    : DeletionCode.SpectrumPath.spectrum_boolean
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:19:18.234849+00:00
-- url     : https://prove2.me/theorems/b165cd3f-b8ac-4617-a613-2125c0e36980
-- title:
--   Spectrum Path: spectrum boolean
-- statement:
--   Every actual integral spectrum coordinate is zero or one.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L77-L85
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L77-L85

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.spectrum_boolean (word : Letters) (n L : ℕ)
    (hunique : KUnique word n (L - 1)) :
    ∀ g, wordSpectrum word n L g = 0 ∨ wordSpectrum word n L g = 1 := by sorry
