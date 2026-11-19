-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_kunique_mono
-- name    : DeletionCode.SpectrumPath.kunique_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:19:46.309911+00:00
-- url     : https://prove2.me/theorems/8767f90d-a1c7-4635-9cea-bc1d119b28ad
-- title:
--   Spectrum Path: kunique mono
-- statement:
--   Uniqueness of shorter windows implies uniqueness of every longer window.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L172-L177
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L172-L177

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.kunique_mono (word : Letters) (n k m : ℕ)
    (hunique : KUnique word n k) (hkm : k ≤ m) : KUnique word n m := by sorry
