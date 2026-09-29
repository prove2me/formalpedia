-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_runBands_nested
-- name    : BookProof.RitzCertificate.runBands_nested
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:50:06.140962+00:00
-- url     : https://prove2.me/theorems/bfbb331d-945f-4fad-8768-a731dd8dc2e4
-- title:
--   (lo hi : ℕ → ℝ) : NestedBands (runLo lo) (runHi hi)
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.runBands_nested` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.runBands_nested
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.runBands_nested (lo hi : ℕ → ℝ) : NestedBands (runLo lo) (runHi hi) := by sorry
