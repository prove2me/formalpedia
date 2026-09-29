-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_ritz_band_enclosure_of_nested
-- name    : BookProof.BandEnclosure.ritz_band_enclosure_of_nested
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:00:29.376769+00:00
-- url     : https://prove2.me/theorems/1bb6d502-6557-4b73-a075-398d8f5f5e64
-- title:
--   [Nontrivial F] (A : F →L[ℂ] F) (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re) (b : HilbertBasis ℕ ℂ F) {lo hi : ℕ → ℝ} (hnest : NestedBands lo hi)...
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.ritz_band_enclosure_of_nested` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.ritz_band_enclosure_of_nested
import Mathlib
import Definitions.Def_ChapterBandEnclosure
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8















open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.BandEnclosure.ritz_band_enclosure_of_nested [Nontrivial F] (A : F →L[ℂ] F) (hsa : IsSelfAdjoint A)
    (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re) (b : HilbertBasis ℕ ℂ F)
    {lo hi : ℕ → ℝ} (hnest : NestedBands lo hi)
    (hritz : ∀ m, ritzInf (finiteModeRestrict A b) (galerkinSpan b (m + 1)) ∈
      Set.Icc (lo m) (hi m)) :
    IsPositiveSelfAdjointExtension (finiteModeRestrict A b) (topRestrict A) ∧
      ∀ m, sInf (spectrum ℝ A) ∈ Set.Icc (lo m) (hi m) := by sorry
