-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_mem_runBand
-- name    : BookProof.RitzCertificate.mem_runBand
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:35:54.68615+00:00
-- url     : https://prove2.me/theorems/8d2f1a69-2783-4f1e-97f8-58411716dae9
-- title:
--   {lo hi : ℕ → ℝ} {lam : ℝ} (h : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) (m : ℕ) : lam ∈ Set.Icc (runLo lo m) (runHi hi m)
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.mem_runBand` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.mem_runBand
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.mem_runBand {lo hi : ℕ → ℝ} {lam : ℝ} (h : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) (m : ℕ) :
    lam ∈ Set.Icc (runLo lo m) (runHi hi m) := by sorry
