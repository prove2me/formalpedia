-- Prove2me | Theorems.Thm_BookProof_RitzCertificate_nested_certificate_of_bands
-- name    : BookProof.RitzCertificate.nested_certificate_of_bands
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:08:00.644997+00:00
-- url     : https://prove2.me/theorems/d3d9109c-767d-4693-99ae-9ebd7cbdbab3
-- title:
--   {lo hi : ℕ → ℝ} {lam : ℝ} (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) : NestedBands (runLo lo) (runHi hi) ∧ (∀ m, lam ∈...
-- statement:
--   Lean 4 theorem `BookProof.RitzCertificate.nested_certificate_of_bands` (module `BookProof.RitzCertificate`), source chapter `BookProof/ChapterRitzCertificate.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzCertificate.lean

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.nested_certificate_of_bands
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

theorem BookProof.RitzCertificate.nested_certificate_of_bands {lo hi : ℕ → ℝ} {lam : ℝ}
    (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    NestedBands (runLo lo) (runHi hi) ∧ (∀ m, lam ∈ Set.Icc (runLo lo m) (runHi hi m)) ∧
      Tendsto (fun m => runHi hi m - runLo lo m) atTop (𝓝 0) := by sorry
