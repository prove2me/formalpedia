-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxLevel_mono_form
-- name    : BookProof.RitzPerturbation.minmaxLevel_mono_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:31:44.648495+00:00
-- url     : https://prove2.me/theorems/0db76207-f315-45e3-92d0-42398e5323c9
-- title:
--   (T T' : F →L[ℂ] F) (k : ℕ) (hle : ∀ x : F, rayleighVal T x ≤ rayleighVal T' x) (hne : (minmaxSet T' k).Nonempty) : minmaxLevel T k ≤ minmaxLevel T' k
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxLevel_mono_form` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxLevel_mono_form
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxLevel_mono_form (T T' : F →L[ℂ] F) (k : ℕ)
    (hle : ∀ x : F, rayleighVal T x ≤ rayleighVal T' x)
    (hne : (minmaxSet T' k).Nonempty) :
    minmaxLevel T k ≤ minmaxLevel T' k := by sorry
