-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_norm_apply_sq
-- name    : BookProof.RitzCertificate.norm_apply_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:36:33.438155+00:00
-- url     : https://prove2.me/theorems/bb5e207c-95e7-4013-ba71-73558f4402c8
-- title:
--   (A : F →L[ℂ] F) (x : F) (hx : ‖x‖ = 1) : ‖A x‖ ^ 2 = resid A x ^ 2 + rayleigh A x ^ 2
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.norm_apply_sq` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.norm_apply_sq
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.norm_apply_sq (A : F →L[ℂ] F) (x : F) (hx : ‖x‖ = 1) :
    ‖A x‖ ^ 2 = resid A x ^ 2 + rayleigh A x ^ 2 := by sorry
