-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_gram_position_unique
-- name    : DeletionCode.SpectrumPath.gram_position_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:22:22.334543+00:00
-- url     : https://prove2.me/theorems/e4e9f860-dcce-420e-9fee-db4144032e67
-- title:
--   Spectrum Path: gram position unique
-- statement:
--   Equal valid L-grams begin at the same position in an (L-1)-unique word.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L49-L55
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L49-L55

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.gram_position_unique (word : Letters) (n L a b : ℕ)
    (hunique : KUnique word n (L - 1))
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (heq : gram word L a = gram word L b) : a = b := by sorry
