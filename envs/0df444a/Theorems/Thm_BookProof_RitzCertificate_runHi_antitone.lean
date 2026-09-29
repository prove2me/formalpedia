-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_runHi_antitone
-- name    : BookProof.RitzCertificate.runHi_antitone
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:37:15.44923+00:00
-- url     : https://prove2.me/theorems/8f507571-0b52-4c96-8b9c-9a5deebaf09f
-- title:
--   (hi : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) : runHi hi n ≤ runHi hi m
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.runHi_antitone` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.runHi_antitone
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.runHi_antitone (hi : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) : runHi hi n ≤ runHi hi m := by sorry
