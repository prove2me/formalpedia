-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxGap_nonneg
-- name    : BookProof.RitzPerturbation.minmaxGap_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:30:31.199809+00:00
-- url     : https://prove2.me/theorems/250cc541-0452-41e7-8d64-df6b81554807
-- title:
--   (T : F →L[ℂ] F) (hne1 : (minmaxSet T 1).Nonempty) : 0 ≤ minmaxGap T
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxGap_nonneg` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxGap_nonneg
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxGap_nonneg (T : F →L[ℂ] F) (hne1 : (minmaxSet T 1).Nonempty) :
    0 ≤ minmaxGap T := by sorry
