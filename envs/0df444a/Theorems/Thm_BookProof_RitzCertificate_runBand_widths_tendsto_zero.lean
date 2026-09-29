-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_runBand_widths_tendsto_zero
-- name    : BookProof.RitzCertificate.runBand_widths_tendsto_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:30:22.630444+00:00
-- url     : https://prove2.me/theorems/90e6713d-df36-44dd-b43f-affec5554f95
-- title:
--   {lo hi : ℕ → ℝ} {lam : ℝ} (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) : Tendsto (fun m => runHi hi m - runLo lo m) atTop (𝓝 0)
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.runBand_widths_tendsto_zero` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.runBand_widths_tendsto_zero
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.runBand_widths_tendsto_zero {lo hi : ℕ → ℝ} {lam : ℝ}
    (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    Tendsto (fun m => runHi hi m - runLo lo m) atTop (𝓝 0) := by sorry
