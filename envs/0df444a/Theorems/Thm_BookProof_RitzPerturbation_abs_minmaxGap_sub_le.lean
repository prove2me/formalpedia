-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_abs_minmaxGap_sub_le
-- name    : BookProof.RitzPerturbation.abs_minmaxGap_sub_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:16:12.361728+00:00
-- url     : https://prove2.me/theorems/22e7cc02-b234-4421-8dbb-6ae411eac3ed
-- title:
--   (T T' : F →L[ℂ] F) (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) : |minmaxGap T - minmaxGap T'| ≤ 2 * ‖T - T'‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.abs_minmaxGap_sub_le` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.abs_minmaxGap_sub_le
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.abs_minmaxGap_sub_le (T T' : F →L[ℂ] F)
    (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) :
    |minmaxGap T - minmaxGap T'| ≤ 2 * ‖T - T'‖ := by sorry
