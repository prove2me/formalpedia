-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_equal_spectrum_eq_finite
-- name    : DeletionCode.SpectrumPath.equal_spectrum_eq_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:15:51.791439+00:00
-- url     : https://prove2.me/theorems/5d0d40bd-6e18-4a69-9381-2b3ef49860de
-- title:
--   Spectrum Path: equal spectrum eq finite
-- statement:
--   In the finite-word representation, equal spectra give literal word equality.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L147-L153
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L147-L153

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.equal_spectrum_eq_finite (word z : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1))
    (hspectrum : wordSpectrum z n L = wordSpectrum word n L) :
    (fun i : Fin n => z i.val) = (fun i : Fin n => word i.val) := by sorry
