-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_spectrum_is_simple_path_and_determines_word
-- name    : DeletionCode.SpectrumPath.spectrum_is_simple_path_and_determines_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:23:14.557336+00:00
-- url     : https://prove2.me/theorems/c4f169e9-c451-4013-98f3-a6d6afdfe626
-- title:
--   Spectrum Path: spectrum is simple path and determines word
-- statement:
--   Manuscript Lemma `lem:path`, stated with actual counts, path vertices, and edge labels.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L156-L169
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L156-L169

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.spectrum_is_simple_path_and_determines_word (word : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1)) :
    (∀ g, wordSpectrum word n L g = 0 ∨ wordSpectrum word n L g = 1) ∧
    Function.Injective (fun i : Fin (n - L + 2) => vertexAt word L i.val) ∧
    (∀ g, wordSpectrum word n L g ≠ 0 ↔ ∃ i : Fin (n - L + 1), gram word L i.val = g) ∧
    (∀ i : Fin (n - L + 1),
      gramPrefix (gram word L i.val) = vertexAt word L i.val ∧
      gramSuffix (gram word L i.val) = vertexAt word L (i.val + 1)) ∧
    (∀ z : Letters, wordSpectrum z n L = wordSpectrum word n L → Agree z 0 word 0 n) := by sorry
