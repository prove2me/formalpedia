-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_neg_norm_le_minmaxLevel
-- name    : BookProof.RitzPerturbation.neg_norm_le_minmaxLevel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:33:47.227047+00:00
-- url     : https://prove2.me/theorems/dbba1f4d-aaa8-4259-ba6b-25c9f42374e6
-- title:
--   (T : F →L[ℂ] F) (k : ℕ) (hne : (minmaxSet T k).Nonempty) : -‖T‖ ≤ minmaxLevel T k
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.neg_norm_le_minmaxLevel` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.neg_norm_le_minmaxLevel
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.neg_norm_le_minmaxLevel (T : F →L[ℂ] F) (k : ℕ) (hne : (minmaxSet T k).Nonempty) :
    -‖T‖ ≤ minmaxLevel T k := by sorry
