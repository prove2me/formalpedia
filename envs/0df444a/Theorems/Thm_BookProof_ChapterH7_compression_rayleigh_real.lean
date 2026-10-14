-- Prove2me | Theorems.Thm_BookProof_ChapterH7_compression_rayleigh_real
-- name    : BookProof.ChapterH7.compression_rayleigh_real
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:07:41.299337+00:00
-- url     : https://prove2.me/theorems/6446aa92-44b8-4798-86eb-f4ba3decec3a
-- title:
--   `BookProof.ChapterH7.compression_rayleigh_real` (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) (y : F) : (inner ℂ y (compress V X y) : ℂ).im = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH7`.
--
--   `BookProof.ChapterH7.compression_rayleigh_real` (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) (y : F) : (inner ℂ y (compress V X y) : ℂ).im = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH7.compression_rayleigh_real`.

-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.compression_rayleigh_real
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterH4
open BookProof.ChapterH4
open BookProof.ChapterH7


noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterH7.compression_rayleigh_real (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hX : IsSelfAdjoint X) (y : F) : (inner ℂ y (compress V X y) : ℂ).im = 0 := by sorry
