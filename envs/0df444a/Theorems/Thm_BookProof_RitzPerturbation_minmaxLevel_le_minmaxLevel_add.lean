-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxLevel_le_minmaxLevel_add
-- name    : BookProof.RitzPerturbation.minmaxLevel_le_minmaxLevel_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:03:56.301579+00:00
-- url     : https://prove2.me/theorems/8427a16c-1554-44f3-a72c-a814f4f82da4
-- title:
--   (T T' : F →L[ℂ] F) (k : ℕ) (hne : (minmaxSet T' k).Nonempty) : minmaxLevel T k ≤ minmaxLevel T' k + ‖T - T'‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxLevel_le_minmaxLevel_add` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxLevel_le_minmaxLevel_add
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxLevel_le_minmaxLevel_add (T T' : F →L[ℂ] F) (k : ℕ)
    (hne : (minmaxSet T' k).Nonempty) :
    minmaxLevel T k ≤ minmaxLevel T' k + ‖T - T'‖ := by sorry
