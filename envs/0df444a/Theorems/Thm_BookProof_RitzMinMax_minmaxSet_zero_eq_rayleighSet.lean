-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_minmaxSet_zero_eq_rayleighSet
-- name    : BookProof.RitzMinMax.minmaxSet_zero_eq_rayleighSet
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:08:48.141794+00:00
-- url     : https://prove2.me/theorems/cb38a53c-96fb-427d-9b01-f6877ea20f84
-- title:
--   (T : F →L[ℂ] F) : minmaxSet T 0 = rayleighSet T
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.minmaxSet_zero_eq_rayleighSet` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxSet_zero_eq_rayleighSet
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.minmaxSet_zero_eq_rayleighSet (T : F →L[ℂ] F) : minmaxSet T 0 = rayleighSet T := by sorry
