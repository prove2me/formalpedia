-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxGap_tendsto_of_tendsto
-- name    : BookProof.RitzPerturbation.minmaxGap_tendsto_of_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:38:48.820266+00:00
-- url     : https://prove2.me/theorems/ffcbb882-a0e4-4d0c-95b8-338337755a47
-- title:
--   {ι : Type*} {l : Filter ι} (Tn : ι → F →L[ℂ] F) (T : F →L[ℂ] F) (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) (h : Tendsto (fun i => ‖Tn i - T‖) l (𝓝 0)) : Tendsto (fun i =>...
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxGap_tendsto_of_tendsto` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxGap_tendsto_of_tendsto
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxGap_tendsto_of_tendsto {ι : Type*} {l : Filter ι} (Tn : ι → F →L[ℂ] F)
    (T : F →L[ℂ] F) (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty)
    (h : Tendsto (fun i => ‖Tn i - T‖) l (𝓝 0)) :
    Tendsto (fun i => minmaxGap (Tn i)) l (𝓝 (minmaxGap T)) := by sorry
