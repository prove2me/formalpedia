-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_runLo_mono
-- name    : BookProof.RitzCertificate.runLo_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:38:52.843218+00:00
-- url     : https://prove2.me/theorems/97628fe8-2282-42c1-a595-b3683ffec4ed
-- title:
--   (lo : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) : runLo lo m ≤ runLo lo n
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.runLo_mono` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.runLo_mono
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.runLo_mono (lo : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) : runLo lo m ≤ runLo lo n := by sorry
