-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_isSelfAdjoint_sub_const
-- name    : BookProof.RitzCertificate.isSelfAdjoint_sub_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:34:17.431663+00:00
-- url     : https://prove2.me/theorems/cca560a9-5c02-4df2-b129-f05eac032d5c
-- title:
--   {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (c : ℝ) : IsSelfAdjoint (A - (c : ℝ) • (1 : F →L[ℂ] F))
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.isSelfAdjoint_sub_const` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.isSelfAdjoint_sub_const
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.isSelfAdjoint_sub_const {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (c : ℝ) :
    IsSelfAdjoint (A - (c : ℝ) • (1 : F →L[ℂ] F)) := by sorry
