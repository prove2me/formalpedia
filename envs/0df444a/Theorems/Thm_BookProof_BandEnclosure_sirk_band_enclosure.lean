-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_sirk_band_enclosure
-- name    : BookProof.BandEnclosure.sirk_band_enclosure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:04:52.005321+00:00
-- url     : https://prove2.me/theorems/8128034c-16df-4bf1-89b1-6c611741088a
-- title:
--   (C Dmin h nv : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 < h) {a : ℕ → ℝ} {lam : ℝ} (hmem : ∀ m, a m ∈ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m)) (hconv :...
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.sirk_band_enclosure` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.sirk_band_enclosure
import Mathlib
import Definitions.Def_ChapterBandEnclosure
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8

theorem BookProof.BandEnclosure.sirk_band_enclosure (C Dmin h nv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 < h)
    {a : ℕ → ℝ} {lam : ℝ}
    (hmem : ∀ m, a m ∈ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m))
    (hconv : Tendsto a atTop (𝓝 lam)) :
    (∀ m, lam ∈ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m)) ∧
      (∀ lam', (∀ m, lam' ∈ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m)) → lam' = lam) ∧
      Tendsto (fun m => sirkBound C Dmin h nv m) atTop (𝓝 lam) := by sorry
