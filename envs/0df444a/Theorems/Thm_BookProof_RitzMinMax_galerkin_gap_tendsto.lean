-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_galerkin_gap_tendsto
-- name    : BookProof.RitzMinMax.galerkin_gap_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:25:06.95648+00:00
-- url     : https://prove2.me/theorems/5c46ceca-9edb-4a4c-bc3d-f294a9972a58
-- title:
--   (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) : Tendsto (fun m : ℕ => minmaxLevelIn T (galerkinSpan b m) 1 - minmaxLevelIn T (galerkinSpan b m) 0) atTop (nhds (minmaxLevel T 1 - minmaxLevel T 0))
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.galerkin_gap_tendsto` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.galerkin_gap_tendsto
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.galerkin_gap_tendsto (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    Tendsto (fun m : ℕ => minmaxLevelIn T (galerkinSpan b m) 1
        - minmaxLevelIn T (galerkinSpan b m) 0) atTop
      (nhds (minmaxLevel T 1 - minmaxLevel T 0)) := by sorry
