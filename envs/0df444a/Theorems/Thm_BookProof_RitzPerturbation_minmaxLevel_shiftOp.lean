-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxLevel_shiftOp
-- name    : BookProof.RitzPerturbation.minmaxLevel_shiftOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:01:47.119319+00:00
-- url     : https://prove2.me/theorems/cc4cdb92-fc29-4409-8433-95fd941651a4
-- title:
--   (T : F →L[ℂ] F) (c : ℝ) (k : ℕ) (hne : (minmaxSet T k).Nonempty) : minmaxLevel (shiftOp T c) k = minmaxLevel T k + c
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxLevel_shiftOp` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxLevel_shiftOp
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxLevel_shiftOp (T : F →L[ℂ] F) (c : ℝ) (k : ℕ)
    (hne : (minmaxSet T k).Nonempty) :
    minmaxLevel (shiftOp T c) k = minmaxLevel T k + c := by sorry
