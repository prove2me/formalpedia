-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_minmaxLevel_zero_eq_rayleighInf
-- name    : BookProof.RitzMinMax.minmaxLevel_zero_eq_rayleighInf
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:15:29.007248+00:00
-- url     : https://prove2.me/theorems/11b5b84b-52a2-409e-8a49-f8097bdea43f
-- title:
--   [Nontrivial F] (T : F →L[ℂ] F) : minmaxLevel T 0 = rayleighInf T
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.minmaxLevel_zero_eq_rayleighInf` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxLevel_zero_eq_rayleighInf
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.minmaxLevel_zero_eq_rayleighInf [Nontrivial F] (T : F →L[ℂ] F) :
    minmaxLevel T 0 = rayleighInf T := by sorry
