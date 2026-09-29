-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_runHi_le
-- name    : BookProof.RitzCertificate.runHi_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:38:03.140422+00:00
-- url     : https://prove2.me/theorems/a3386b3b-264c-4bb2-b048-469991e3987c
-- title:
--   (hi : ℕ → ℝ) (m : ℕ) : runHi hi m ≤ hi m
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.runHi_le` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.runHi_le
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.runHi_le (hi : ℕ → ℝ) (m : ℕ) : runHi hi m ≤ hi m := by sorry
