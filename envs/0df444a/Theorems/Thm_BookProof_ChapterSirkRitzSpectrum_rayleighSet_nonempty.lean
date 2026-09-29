-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_rayleighSet_nonempty
-- name    : BookProof.ChapterSirkRitzSpectrum.rayleighSet_nonempty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:26:39.590932+00:00
-- url     : https://prove2.me/theorems/51979619-592b-434d-ae9b-74db26f3df1a
-- title:
--   [Nontrivial F] (T : F →L[ℂ] F) : (rayleighSet T).Nonempty
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.rayleighSet_nonempty` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.rayleighSet_nonempty
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.rayleighSet_nonempty [Nontrivial F] (T : F →L[ℂ] F) : (rayleighSet T).Nonempty := by sorry
