-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxGap_ge_of_dist_le
-- name    : BookProof.RitzPerturbation.minmaxGap_ge_of_dist_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:17:30.849555+00:00
-- url     : https://prove2.me/theorems/a098e54e-d7cf-40dc-90b3-6a2ad5a747d6
-- title:
--   (T T' : F →L[ℂ] F) {eps : ℝ} (hd : ‖T - T'‖ ≤ eps) (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) : minmaxGap T' - 2 * eps ≤ minmaxGap T
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxGap_ge_of_dist_le` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxGap_ge_of_dist_le
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxGap_ge_of_dist_le (T T' : F →L[ℂ] F) {eps : ℝ} (hd : ‖T - T'‖ ≤ eps)
    (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) :
    minmaxGap T' - 2 * eps ≤ minmaxGap T := by sorry
