-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxGap_shiftOp
-- name    : BookProof.RitzPerturbation.minmaxGap_shiftOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:09:28.030609+00:00
-- url     : https://prove2.me/theorems/3d7eb5a1-88aa-41c9-a069-2d0f4bafa09e
-- title:
--   (T : F →L[ℂ] F) (c : ℝ) (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) : minmaxGap (shiftOp T c) = minmaxGap T
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxGap_shiftOp` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxGap_shiftOp
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxGap_shiftOp (T : F →L[ℂ] F) (c : ℝ)
    (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) :
    minmaxGap (shiftOp T c) = minmaxGap T := by sorry
