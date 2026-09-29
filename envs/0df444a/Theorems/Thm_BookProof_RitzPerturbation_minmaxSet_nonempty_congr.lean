-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxSet_nonempty_congr
-- name    : BookProof.RitzPerturbation.minmaxSet_nonempty_congr
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:33:09.372569+00:00
-- url     : https://prove2.me/theorems/afc81465-7e86-47cb-98aa-d4504fb7d174
-- title:
--   (T T' : F →L[ℂ] F) {k : ℕ} (h : (minmaxSet T k).Nonempty) : (minmaxSet T' k).Nonempty
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxSet_nonempty_congr` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxSet_nonempty_congr
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxSet_nonempty_congr (T T' : F →L[ℂ] F) {k : ℕ}
    (h : (minmaxSet T k).Nonempty) : (minmaxSet T' k).Nonempty := by sorry
