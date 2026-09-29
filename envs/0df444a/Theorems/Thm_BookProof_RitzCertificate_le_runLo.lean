-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_le_runLo
-- name    : BookProof.RitzCertificate.le_runLo
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:35:11.754067+00:00
-- url     : https://prove2.me/theorems/86805ac4-6562-4f61-95ef-bb97dc2ac873
-- title:
--   (lo : ℕ → ℝ) (m : ℕ) : lo m ≤ runLo lo m
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.le_runLo` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.le_runLo
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.le_runLo (lo : ℕ → ℝ) (m : ℕ) : lo m ≤ runLo lo m := by sorry
