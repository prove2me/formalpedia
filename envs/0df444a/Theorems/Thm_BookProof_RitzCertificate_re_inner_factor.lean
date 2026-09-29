-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_re_inner_factor
-- name    : BookProof.RitzCertificate.re_inner_factor
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:58:14.390641+00:00
-- url     : https://prove2.me/theorems/a19a5089-818e-4bb0-8e56-206bb17d055d
-- title:
--   {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (l b : ℝ) (x : F) : (inner ℂ x ((((A - (l : ℝ) • (1 : F →L[ℂ] F)) * (A - (b : ℝ) • (1 : F →L[ℂ] F))) x)) : ℂ).re = ‖A x‖ ^ 2 -...
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.re_inner_factor` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.re_inner_factor
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.re_inner_factor {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (l b : ℝ) (x : F) :
    (inner ℂ x ((((A - (l : ℝ) • (1 : F →L[ℂ] F)) *
        (A - (b : ℝ) • (1 : F →L[ℂ] F))) x)) : ℂ).re
      = ‖A x‖ ^ 2 - (l + b) * rayleigh A x + l * b * ‖x‖ ^ 2 := by sorry
