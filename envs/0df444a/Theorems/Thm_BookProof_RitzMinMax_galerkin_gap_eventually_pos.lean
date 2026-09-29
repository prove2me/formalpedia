-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_galerkin_gap_eventually_pos
-- name    : BookProof.RitzMinMax.galerkin_gap_eventually_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:25:42.354183+00:00
-- url     : https://prove2.me/theorems/eb2bc8a3-20fb-4e9b-bc5e-9b48c1ca0020
-- title:
--   (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (hgap : minmaxLevel T 0 < minmaxLevel T 1) : ∀ᶠ m : ℕ in atTop, 0 < minmaxLevelIn T (galerkinSpan b m) 1 - minmaxLevelIn T (galerkinSpan b m) 0
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.galerkin_gap_eventually_pos` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.galerkin_gap_eventually_pos
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.galerkin_gap_eventually_pos (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    (hgap : minmaxLevel T 0 < minmaxLevel T 1) :
    ∀ᶠ m : ℕ in atTop, 0 < minmaxLevelIn T (galerkinSpan b m) 1
      - minmaxLevelIn T (galerkinSpan b m) 0 := by sorry
