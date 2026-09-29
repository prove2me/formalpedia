-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzInf_tendsto_sInf_spectrum
-- name    : BookProof.ChapterSirkRitzSpectrum.ritzInf_tendsto_sInf_spectrum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:20:30.940469+00:00
-- url     : https://prove2.me/theorems/4dc1d56e-9be1-43ec-8fb1-34ac55d5a961
-- title:
--   [Nontrivial F] (A : F →L[ℂ] F) (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re) (b : HilbertBasis ℕ ℂ F) : Tendsto (fun m : ℕ => ritzInf...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.ritzInf_tendsto_sInf_spectrum` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.ritzInf_tendsto_sInf_spectrum
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.ritzInf_tendsto_sInf_spectrum [Nontrivial F] (A : F →L[ℂ] F) (hsa : IsSelfAdjoint A)
    (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re) (b : HilbertBasis ℕ ℂ F) :
    Tendsto (fun m : ℕ => ritzInf (finiteModeRestrict A b) (galerkinSpan b (m + 1))) atTop
      (nhds (sInf (spectrum ℝ A))) := by sorry
