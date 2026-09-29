-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_temple_nested_certificate
-- name    : BookProof.RitzCertificate.temple_nested_certificate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:18:52.131131+00:00
-- url     : https://prove2.me/theorems/2cadbfdb-2e6b-4c68-adfe-0632999aeb84
-- title:
--   [Nontrivial F] {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {b delta : ℝ} {x : ℕ → F} (hsep : SpectralSeparation A (sInf (spectrum ℝ A)) b) (hdelta : 0 < delta) (hx : ∀ m, ‖x m‖ = 1)...
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.temple_nested_certificate` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.temple_nested_certificate
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure
open BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]





















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.temple_nested_certificate [Nontrivial F] {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {b delta : ℝ} {x : ℕ → F} (hsep : SpectralSeparation A (sInf (spectrum ℝ A)) b)
    (hdelta : 0 < delta) (hx : ∀ m, ‖x m‖ = 1) (hle : ∀ m, rayleigh A (x m) ≤ b - delta)
    (hres : Tendsto (fun m => resid A (x m)) atTop (𝓝 0)) :
    NestedBands (runLo fun m => rayleigh A (x m) - resid A (x m) ^ 2 / (b - rayleigh A (x m)))
        (runHi fun m => rayleigh A (x m)) ∧
      (∀ m, sInf (spectrum ℝ A) ∈
        Set.Icc (runLo (fun m => rayleigh A (x m) -
            resid A (x m) ^ 2 / (b - rayleigh A (x m))) m)
          (runHi (fun m => rayleigh A (x m)) m)) ∧
      Tendsto (fun m => runHi (fun m => rayleigh A (x m)) m -
        runLo (fun m => rayleigh A (x m) -
          resid A (x m) ^ 2 / (b - rayleigh A (x m))) m) atTop (𝓝 0) := by sorry
