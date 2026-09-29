-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_temple_band_mem
-- name    : BookProof.RitzCertificate.temple_band_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:07:51.935847+00:00
-- url     : https://prove2.me/theorems/361ecf10-b34d-4716-bc3d-20a753c44b8b
-- title:
--   [Nontrivial F] {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {b : ℝ} {x : F} (hsep : SpectralSeparation A (sInf (spectrum ℝ A)) b) (hx : ‖x‖ = 1) (hlt : rayleigh A x < b) : sInf (spectrum...
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.temple_band_mem` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.temple_band_mem
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.temple_band_mem [Nontrivial F] {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {b : ℝ} {x : F}
    (hsep : SpectralSeparation A (sInf (spectrum ℝ A)) b) (hx : ‖x‖ = 1)
    (hlt : rayleigh A x < b) :
    sInf (spectrum ℝ A) ∈
      Set.Icc (rayleigh A x - resid A x ^ 2 / (b - rayleigh A x)) (rayleigh A x) := by sorry
