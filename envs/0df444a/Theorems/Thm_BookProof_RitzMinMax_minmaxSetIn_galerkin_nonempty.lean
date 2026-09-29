-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_minmaxSetIn_galerkin_nonempty
-- name    : BookProof.RitzMinMax.minmaxSetIn_galerkin_nonempty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:51:49.971762+00:00
-- url     : https://prove2.me/theorems/3995ec53-9967-49eb-927c-06b0b2dd5342
-- title:
--   (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) {k m : ℕ} (hm : k + 1 ≤ m) : (minmaxSetIn T (galerkinSpan b m) k).Nonempty
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.minmaxSetIn_galerkin_nonempty` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxSetIn_galerkin_nonempty
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.minmaxSetIn_galerkin_nonempty (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) {k m : ℕ}
    (hm : k + 1 ≤ m) : (minmaxSetIn T (galerkinSpan b m) k).Nonempty := by sorry
