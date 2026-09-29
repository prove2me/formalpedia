-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_minmaxLevel_mono
-- name    : BookProof.RitzMinMax.minmaxLevel_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:20:50.039977+00:00
-- url     : https://prove2.me/theorems/e7f87cc5-74a6-4bf1-a6fd-c669fa7c477d
-- title:
--   (T : F →L[ℂ] F) {k l : ℕ} (hkl : k ≤ l) (hne : (minmaxSet T l).Nonempty) : minmaxLevel T k ≤ minmaxLevel T l
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.minmaxLevel_mono` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxLevel_mono
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.minmaxLevel_mono (T : F →L[ℂ] F) {k l : ℕ} (hkl : k ≤ l)
    (hne : (minmaxSet T l).Nonempty) : minmaxLevel T k ≤ minmaxLevel T l := by sorry
