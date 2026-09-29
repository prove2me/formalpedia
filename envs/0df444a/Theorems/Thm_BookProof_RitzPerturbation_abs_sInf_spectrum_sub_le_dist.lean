-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_abs_sInf_spectrum_sub_le_dist
-- name    : BookProof.RitzPerturbation.abs_sInf_spectrum_sub_le_dist
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:16:46.995423+00:00
-- url     : https://prove2.me/theorems/91d4c945-c22e-44bc-9b11-8fec956530e7
-- title:
--   [Nontrivial F] (T T' : F →L[ℂ] F) (hT : IsSelfAdjoint T) (hT' : IsSelfAdjoint T') (hne : (minmaxSet T 0).Nonempty) : |sInf (spectrum ℝ T) - sInf (spectrum ℝ T')| ≤ ‖T - T'‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.abs_sInf_spectrum_sub_le_dist` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.abs_sInf_spectrum_sub_le_dist
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.abs_sInf_spectrum_sub_le_dist [Nontrivial F] (T T' : F →L[ℂ] F)
    (hT : IsSelfAdjoint T) (hT' : IsSelfAdjoint T')
    (hne : (minmaxSet T 0).Nonempty) :
    |sInf (spectrum ℝ T) - sInf (spectrum ℝ T')| ≤ ‖T - T'‖ := by sorry
