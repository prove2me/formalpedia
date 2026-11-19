-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_spectrum_support_path
-- name    : DeletionCode.SpectrumPath.spectrum_support_path
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:22:44.22358+00:00
-- url     : https://prove2.me/theorems/39e117e2-ccb5-4684-aba5-a49fc67ed619
-- title:
--   Spectrum Path: spectrum support path
-- statement:
--   These are exactly the n-L+1 edges carried by the spectrum.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L102-L109
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L102-L109

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.spectrum_support_path (word : Letters) (n L : ℕ) (hn : L ≤ n) (g : Gram L) :
    wordSpectrum word n L g ≠ 0 ↔ ∃ i : Fin (n - L + 1), gram word L i.val = g := by sorry
