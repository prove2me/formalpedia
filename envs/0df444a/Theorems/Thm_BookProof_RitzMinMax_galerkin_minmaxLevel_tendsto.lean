-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_galerkin_minmaxLevel_tendsto
-- name    : BookProof.RitzMinMax.galerkin_minmaxLevel_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:23:48.281331+00:00
-- url     : https://prove2.me/theorems/dd0a3d55-19e8-4c2c-808a-4c4beba18b8c
-- title:
--   (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (k : ℕ) : Tendsto (fun m : ℕ => minmaxLevelIn T (galerkinSpan b m) k) atTop (nhds (minmaxLevel T k))
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.galerkin_minmaxLevel_tendsto` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.galerkin_minmaxLevel_tendsto
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.galerkin_minmaxLevel_tendsto (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (k : ℕ) :
    Tendsto (fun m : ℕ => minmaxLevelIn T (galerkinSpan b m) k) atTop
      (nhds (minmaxLevel T k)) := by sorry
