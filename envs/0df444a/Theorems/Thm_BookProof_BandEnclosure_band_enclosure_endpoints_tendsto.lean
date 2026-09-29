-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_band_enclosure_endpoints_tendsto
-- name    : BookProof.BandEnclosure.band_enclosure_endpoints_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:00:15.025101+00:00
-- url     : https://prove2.me/theorems/9a3e0c64-15cf-4ed3-b64c-e2765f041a64
-- title:
--   {lo hi a : ℕ → ℝ} {lam : ℝ} (hnest : NestedBands lo hi) (hmem : ∀ m, a m ∈ Set.Icc (lo m) (hi m)) (hconv : Tendsto a atTop (𝓝 lam)) (hwidth : Tendsto (fun m => hi m - lo m) atTop...
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.band_enclosure_endpoints_tendsto` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.band_enclosure_endpoints_tendsto
import Mathlib
import Definitions.Def_ChapterBandEnclosure
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8

theorem BookProof.BandEnclosure.band_enclosure_endpoints_tendsto {lo hi a : ℕ → ℝ} {lam : ℝ}
    (hnest : NestedBands lo hi) (hmem : ∀ m, a m ∈ Set.Icc (lo m) (hi m))
    (hconv : Tendsto a atTop (𝓝 lam))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    (∀ m, lam ∈ Set.Icc (lo m) (hi m)) ∧
      (∀ lam', (∀ m, lam' ∈ Set.Icc (lo m) (hi m)) → lam' = lam) ∧
      Tendsto lo atTop (𝓝 lam) ∧ Tendsto hi atTop (𝓝 lam) := by sorry
