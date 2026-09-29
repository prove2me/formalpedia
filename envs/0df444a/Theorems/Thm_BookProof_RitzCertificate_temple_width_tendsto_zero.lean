-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_temple_width_tendsto_zero
-- name    : BookProof.RitzCertificate.temple_width_tendsto_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:53:11.459987+00:00
-- url     : https://prove2.me/theorems/9d5196a1-0f2d-4a87-a3bf-b59ee6d0bac0
-- title:
--   {A : F →L[ℂ] F} {b delta : ℝ} {x : ℕ → F} (hdelta : 0 < delta) (hle : ∀ m, rayleigh A (x m) ≤ b - delta) (hres : Tendsto (fun m => resid A (x m)) atTop (𝓝 0)) : Tendsto (fun m =>...
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.temple_width_tendsto_zero` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.temple_width_tendsto_zero
import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzCertificate.temple_width_tendsto_zero {A : F →L[ℂ] F} {b delta : ℝ} {x : ℕ → F}
    (hdelta : 0 < delta) (hle : ∀ m, rayleigh A (x m) ≤ b - delta)
    (hres : Tendsto (fun m => resid A (x m)) atTop (𝓝 0)) :
    Tendsto (fun m => rayleigh A (x m) -
      (rayleigh A (x m) - resid A (x m) ^ 2 / (b - rayleigh A (x m)))) atTop (𝓝 0) := by sorry
