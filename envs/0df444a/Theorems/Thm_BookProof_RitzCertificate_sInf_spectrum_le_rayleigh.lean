-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_sInf_spectrum_le_rayleigh
-- name    : BookProof.RitzCertificate.sInf_spectrum_le_rayleigh
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:48:19.791055+00:00
-- url     : https://prove2.me/theorems/3d6b2608-2722-4f1f-a3a9-aa862b0815da
-- title:
--   [Nontrivial F] (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {x : F} (hx : ‖x‖ = 1) : sInf (spectrum ℝ A) ≤ rayleigh A x
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.sInf_spectrum_le_rayleigh` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.sInf_spectrum_le_rayleigh
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.sInf_spectrum_le_rayleigh [Nontrivial F] (A : F →L[ℂ] F) (hA : IsSelfAdjoint A)
    {x : F} (hx : ‖x‖ = 1) : sInf (spectrum ℝ A) ≤ rayleigh A x := by sorry
