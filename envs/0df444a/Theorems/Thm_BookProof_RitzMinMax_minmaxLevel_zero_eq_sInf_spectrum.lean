-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_minmaxLevel_zero_eq_sInf_spectrum
-- name    : BookProof.RitzMinMax.minmaxLevel_zero_eq_sInf_spectrum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:21:20.406084+00:00
-- url     : https://prove2.me/theorems/c5b33935-e6e1-4e0a-a1b2-7512f4240a60
-- title:
--   [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) : minmaxLevel T 0 = sInf (spectrum ℝ T)
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.minmaxLevel_zero_eq_sInf_spectrum` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxLevel_zero_eq_sInf_spectrum
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.minmaxLevel_zero_eq_sInf_spectrum [Nontrivial F] (T : F →L[ℂ] F)
    (hT : IsSelfAdjoint T) : minmaxLevel T 0 = sInf (spectrum ℝ T) := by sorry
