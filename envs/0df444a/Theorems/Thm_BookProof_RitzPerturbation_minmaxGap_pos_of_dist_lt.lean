-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxGap_pos_of_dist_lt
-- name    : BookProof.RitzPerturbation.minmaxGap_pos_of_dist_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:22:19.054491+00:00
-- url     : https://prove2.me/theorems/0c183c70-f575-49c1-aa57-2f082252a964
-- title:
--   (T T' : F →L[ℂ] F) {eps : ℝ} (hd : ‖T - T'‖ ≤ eps) (hgap : 2 * eps < minmaxGap T') (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) : 0 < minmaxGap T
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxGap_pos_of_dist_lt` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxGap_pos_of_dist_lt
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxGap_pos_of_dist_lt (T T' : F →L[ℂ] F) {eps : ℝ} (hd : ‖T - T'‖ ≤ eps)
    (hgap : 2 * eps < minmaxGap T')
    (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) :
    0 < minmaxGap T := by sorry
