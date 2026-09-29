-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_factor_nonneg_of_separation
-- name    : BookProof.RitzCertificate.factor_nonneg_of_separation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:48:29.829124+00:00
-- url     : https://prove2.me/theorems/6b6e67d4-7234-4cfc-bbb7-60e7b5e8dba2
-- title:
--   {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b : ℝ} (hsep : SpectralSeparation A l b) : 0 ≤ (A - (l : ℝ) • (1 : F →L[ℂ] F)) * (A - (b : ℝ) • (1 : F →L[ℂ] F))
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.factor_nonneg_of_separation` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.factor_nonneg_of_separation
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.factor_nonneg_of_separation {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b : ℝ}
    (hsep : SpectralSeparation A l b) :
    0 ≤ (A - (l : ℝ) • (1 : F →L[ℂ] F)) * (A - (b : ℝ) • (1 : F →L[ℂ] F)) := by sorry
