-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_replacement
-- name    : DeletionCode.SpectrumLocalization.replacement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:34:46.464233+00:00
-- url     : https://prove2.me/theorems/fa4d960c-f6e8-4c9b-a398-ff0676700703
-- title:
--   Spectrum Localization: replacement
-- statement:
--   A replacement with the same prefix and suffix of length L-1 has the
--   same spectrum change as its local words. Exterior lengths may be arbitrary.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L81-L103
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L81-L103

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.replacement (x y : Letters) (a p q b L : ℕ) (hL : 1 ≤ L)
    (hp : L ≤ p + 1) (hq : L ≤ q + 1)
    (hleft : Agree x 0 y 0 (a + (L - 1)))
    (hright : Agree x (a + (p + 1 - L)) y (a + (q + 1 - L)) (b + (L - 1)))
    (g : Gram L) :
    wordSpectrum y (a + q + b) L g - wordSpectrum x (a + p + b) L g =
      wordSpectrum (fun i => y (a + i)) q L g -
        wordSpectrum (fun i => x (a + i)) p L g := by sorry
