-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_galerkin_ritz_tendsto_sInf_spectrum_of_selected
-- name    : BookProof.ChapterSirkRitzSpectrum.galerkin_ritz_tendsto_sInf_spectrum_of_selected
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:22:11.764911+00:00
-- url     : https://prove2.me/theorems/ff4935ec-3e8a-45ba-a5b8-2ede6e5fa283
-- title:
--   [Nontrivial F] (A : F →L[ℂ] F) (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re) (b : HilbertBasis ℕ ℂ F) : IsPositiveSelfAdjointExtension (finiteModeRestrict...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.galerkin_ritz_tendsto_sInf_spectrum_of_selected` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.galerkin_ritz_tendsto_sInf_spectrum_of_selected
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.galerkin_ritz_tendsto_sInf_spectrum_of_selected [Nontrivial F] (A : F →L[ℂ] F)
    (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re)
    (b : HilbertBasis ℕ ℂ F) :
    IsPositiveSelfAdjointExtension (finiteModeRestrict A b) (topRestrict A) ∧
      Tendsto (fun m : ℕ => ritzInf (finiteModeRestrict A b) (galerkinSpan b (m + 1))) atTop
        (nhds (sInf (spectrum ℝ A))) := by sorry
