-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_temple_lower_bound
-- name    : BookProof.RitzCertificate.temple_lower_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:29:39.674921+00:00
-- url     : https://prove2.me/theorems/4617dced-263e-4e38-90c9-bb753391fe5c
-- title:
--   {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b : ℝ} {x : F} (hsep : SpectralSeparation A l b) (hx : ‖x‖ = 1) (hlt : rayleigh A x < b) : rayleigh A x - resid A x ^ 2 / (b - rayleigh A x) ≤ l
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.temple_lower_bound` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.temple_lower_bound
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.temple_lower_bound {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b : ℝ} {x : F}
    (hsep : SpectralSeparation A l b) (hx : ‖x‖ = 1) (hlt : rayleigh A x < b) :
    rayleigh A x - resid A x ^ 2 / (b - rayleigh A x) ≤ l := by sorry
