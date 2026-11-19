-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_context_replacement
-- name    : DeletionCode.SpectrumLocalization.context_replacement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:23:05.299023+00:00
-- url     : https://prove2.me/theorems/368bd165-2ded-4a5a-871f-687fe7bdf956
-- title:
--   Spectrum Localization: context replacement
-- statement:
--   Concrete unchanged exterior words cancel when the local words share
--   their first and last L-1 letters, exactly as in the coverage proof.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L140-L178
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L140-L178

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.context_replacement (x p q y : List Bool) (L : ℕ) (hL : 1 ≤ L)
    (hp : L ≤ p.length + 1) (hq : L ≤ q.length + 1)
    (hprefix : Agree (listLetters p) 0 (listLetters q) 0 (L - 1))
    (hsuffix : Agree (listLetters p) (p.length + 1 - L)
      (listLetters q) (q.length + 1 - L) (L - 1)) (g : Gram L) :
    wordSpectrum (listLetters (x ++ (q ++ y))) (x.length + q.length + y.length) L g -
      wordSpectrum (listLetters (x ++ (p ++ y))) (x.length + p.length + y.length) L g =
      wordSpectrum (listLetters q) q.length L g - wordSpectrum (listLetters p) p.length L g := by sorry
