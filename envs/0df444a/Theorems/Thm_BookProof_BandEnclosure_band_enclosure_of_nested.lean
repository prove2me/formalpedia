-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_band_enclosure_of_nested
-- name    : BookProof.BandEnclosure.band_enclosure_of_nested
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:51:04.862958+00:00
-- url     : https://prove2.me/theorems/2e047980-b8ec-4484-90cf-a266093193eb
-- title:
--   {lo hi a : ℕ → ℝ} {lam : ℝ} (hnest : NestedBands lo hi) (hmem : ∀ m, a m ∈ Set.Icc (lo m) (hi m)) (hconv : Tendsto a atTop (𝓝 lam)) : ∀ m, lam ∈ Set.Icc (lo m) (hi m)
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.band_enclosure_of_nested` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.band_enclosure_of_nested
import Mathlib
import Definitions.Def_ChapterBandEnclosure
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8

theorem BookProof.BandEnclosure.band_enclosure_of_nested {lo hi a : ℕ → ℝ} {lam : ℝ}
    (hnest : NestedBands lo hi) (hmem : ∀ m, a m ∈ Set.Icc (lo m) (hi m))
    (hconv : Tendsto a atTop (𝓝 lam)) :
    ∀ m, lam ∈ Set.Icc (lo m) (hi m) := by sorry
