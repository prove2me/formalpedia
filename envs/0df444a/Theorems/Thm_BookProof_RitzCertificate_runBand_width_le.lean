-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_runBand_width_le
-- name    : BookProof.RitzCertificate.runBand_width_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:49:27.240417+00:00
-- url     : https://prove2.me/theorems/2334197b-1df3-433b-a8ad-6f933a051541
-- title:
--   (lo hi : ℕ → ℝ) (m : ℕ) : runHi hi m - runLo lo m ≤ hi m - lo m
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.runBand_width_le` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.runBand_width_le
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.runBand_width_le (lo hi : ℕ → ℝ) (m : ℕ) :
    runHi hi m - runLo lo m ≤ hi m - lo m := by sorry
