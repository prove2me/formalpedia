-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxLevel_le_norm
-- name    : BookProof.RitzPerturbation.minmaxLevel_le_norm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:31:06.912335+00:00
-- url     : https://prove2.me/theorems/77b4583f-e3ef-4eb9-970e-282f21b0293a
-- title:
--   (T : F →L[ℂ] F) (k : ℕ) (hne : (minmaxSet T k).Nonempty) : minmaxLevel T k ≤ ‖T‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxLevel_le_norm` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxLevel_le_norm
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxLevel_le_norm (T : F →L[ℂ] F) (k : ℕ) (hne : (minmaxSet T k).Nonempty) :
    minmaxLevel T k ≤ ‖T‖ := by sorry
