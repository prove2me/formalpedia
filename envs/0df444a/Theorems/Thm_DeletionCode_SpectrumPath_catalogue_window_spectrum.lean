-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPath_catalogue_window_spectrum
-- name    : DeletionCode.SpectrumPath.catalogue_window_spectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:15:51.746328+00:00
-- url     : https://prove2.me/theorems/330d8294-6d5b-4327-8143-8becff69f517
-- title:
--   Spectrum Path: catalogue window spectrum
-- statement:
--   The paper's k-uniqueness hypothesis suffices at its chosen L=3(k+1).
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L180-L195
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean#L180-L195

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators

theorem DeletionCode.SpectrumPath.catalogue_window_spectrum (word : Letters) (n k : ℕ)
    (hunique : KUnique word n k) (hn : HeaderRecovery.windowLength k ≤ n) :
    let L := HeaderRecovery.windowLength k
    (∀ g, wordSpectrum word n L g = 0 ∨ wordSpectrum word n L g = 1) ∧
    Function.Injective (fun i : Fin (n - L + 2) => vertexAt word L i.val) ∧
    (∀ g, wordSpectrum word n L g ≠ 0 ↔ ∃ i : Fin (n - L + 1), gram word L i.val = g) ∧
    (∀ i : Fin (n - L + 1),
      gramPrefix (gram word L i.val) = vertexAt word L i.val ∧
      gramSuffix (gram word L i.val) = vertexAt word L (i.val + 1)) ∧
    (∀ z : Letters, wordSpectrum z n L = wordSpectrum word n L → Agree z 0 word 0 n) := by sorry
