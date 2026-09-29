-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_factor_nonneg
-- name    : BookProof.RitzCertificate.factor_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:33:21.501262+00:00
-- url     : https://prove2.me/theorems/bbd12f70-c3f8-4d50-a517-fdb274d4a9d0
-- title:
--   {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b : ℝ} (hspec : ∀ t ∈ spectrum ℝ A, 0 ≤ (t - l) * (t - b)) : 0 ≤ (A - (l : ℝ) • (1 : F →L[ℂ] F)) * (A - (b : ℝ) • (1 : F →L[ℂ] F))
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.factor_nonneg` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.factor_nonneg
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.factor_nonneg {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b : ℝ}
    (hspec : ∀ t ∈ spectrum ℝ A, 0 ≤ (t - l) * (t - b)) :
    0 ≤ (A - (l : ℝ) • (1 : F →L[ℂ] F)) * (A - (b : ℝ) • (1 : F →L[ℂ] F)) := by sorry
