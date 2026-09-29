-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_minmaxSet_nonempty
-- name    : BookProof.RitzMinMax.minmaxSet_nonempty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:00:25.425017+00:00
-- url     : https://prove2.me/theorems/7919b21b-6dd1-4a11-ae38-fcd89ecf5333
-- title:
--   (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (k : ℕ) : (minmaxSet T k).Nonempty
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.minmaxSet_nonempty` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxSet_nonempty
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.minmaxSet_nonempty (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (k : ℕ) :
    (minmaxSet T k).Nonempty := by sorry
