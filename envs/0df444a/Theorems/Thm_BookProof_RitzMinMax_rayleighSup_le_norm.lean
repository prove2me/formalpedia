-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_rayleighSup_le_norm
-- name    : BookProof.RitzMinMax.rayleighSup_le_norm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:59:49.287346+00:00
-- url     : https://prove2.me/theorems/2ce8de61-0a4e-4b9a-af34-0ac4e342e3fc
-- title:
--   (T : F →L[ℂ] F) (S : Submodule ℂ F) : rayleighSup T S ≤ ‖T‖
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.rayleighSup_le_norm` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.rayleighSup_le_norm
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.rayleighSup_le_norm (T : F →L[ℂ] F) (S : Submodule ℂ F) : rayleighSup T S ≤ ‖T‖ := by sorry
