-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxLevel_tendsto_of_tendsto
-- name    : BookProof.RitzPerturbation.minmaxLevel_tendsto_of_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:37:21.376207+00:00
-- url     : https://prove2.me/theorems/5a7505aa-3d55-49ec-8abd-94da111b9957
-- title:
--   {ι : Type*} {l : Filter ι} (Tn : ι → F →L[ℂ] F) (T : F →L[ℂ] F) (k : ℕ) (hne : (minmaxSet T k).Nonempty) (h : Tendsto (fun i => ‖Tn i - T‖) l (𝓝 0)) : Tendsto (fun i => minmaxLevel (Tn i) k) l (𝓝...
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxLevel_tendsto_of_tendsto` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxLevel_tendsto_of_tendsto
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxLevel_tendsto_of_tendsto {ι : Type*} {l : Filter ι} (Tn : ι → F →L[ℂ] F)
    (T : F →L[ℂ] F) (k : ℕ) (hne : (minmaxSet T k).Nonempty)
    (h : Tendsto (fun i => ‖Tn i - T‖) l (𝓝 0)) :
    Tendsto (fun i => minmaxLevel (Tn i) k) l (𝓝 (minmaxLevel T k)) := by sorry
