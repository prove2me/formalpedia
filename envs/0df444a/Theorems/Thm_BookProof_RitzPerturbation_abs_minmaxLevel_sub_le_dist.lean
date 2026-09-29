-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_abs_minmaxLevel_sub_le_dist
-- name    : BookProof.RitzPerturbation.abs_minmaxLevel_sub_le_dist
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:11:47.356378+00:00
-- url     : https://prove2.me/theorems/48546c9b-9703-48aa-b7d2-39db4048af6d
-- title:
--   (T T' : F →L[ℂ] F) (k : ℕ) (hne : (minmaxSet T k).Nonempty) : |minmaxLevel T k - minmaxLevel T' k| ≤ ‖T - T'‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.abs_minmaxLevel_sub_le_dist` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.abs_minmaxLevel_sub_le_dist
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.abs_minmaxLevel_sub_le_dist (T T' : F →L[ℂ] F) (k : ℕ)
    (hne : (minmaxSet T k).Nonempty) :
    |minmaxLevel T k - minmaxLevel T' k| ≤ ‖T - T'‖ := by sorry
