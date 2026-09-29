-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_band_limit_unique
-- name    : BookProof.BandEnclosure.band_limit_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:57:27.76355+00:00
-- url     : https://prove2.me/theorems/f6d9dfdc-b6e8-4101-9e53-cbbcdcddfcb4
-- title:
--   {lo hi : ℕ → ℝ} {lam lam' : ℝ} (h : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) (h' : ∀ m, lam' ∈ Set.Icc (lo m) (hi m)) (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) : lam = lam'
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.band_limit_unique` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.band_limit_unique
import Mathlib
import Definitions.Def_ChapterBandEnclosure
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8

theorem BookProof.BandEnclosure.band_limit_unique {lo hi : ℕ → ℝ} {lam lam' : ℝ}
    (h : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) (h' : ∀ m, lam' ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    lam = lam' := by sorry
