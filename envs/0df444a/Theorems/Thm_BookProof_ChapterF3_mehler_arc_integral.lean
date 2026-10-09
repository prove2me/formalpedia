-- Prove2me | Theorems.Thm_BookProof_ChapterF3_mehler_arc_integral
-- name    : BookProof.ChapterF3.mehler_arc_integral
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:48:59.787377+00:00
-- url     : https://prove2.me/theorems/a66e3139-bbc0-4e96-8929-18d0d7c38f00
-- title:
--   `BookProof.ChapterF3.mehler_arc_integral` (w : ℝ) (hw : 0 < w) : (∫ _x in (0 : ℝ)..w, Real.sqrt (1 / w) * Real.sqrt (1 / (2 * Real.pi))) = Real.sqrt (w / (2 * Real.pi))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF3`.
--
--   `BookProof.ChapterF3.mehler_arc_integral` (w : ℝ) (hw : 0 < w) : (∫ _x in (0 : ℝ)..w, Real.sqrt (1 / w) * Real.sqrt (1 / (2 * Real.pi))) = Real.sqrt (w / (2 * Real.pi))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF3.mehler_arc_integral`.

-- Generated from ChapterF3.lean — theorem BookProof.ChapterF3.mehler_arc_integral
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3


open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterF3.mehler_arc_integral (w : ℝ) (hw : 0 < w) :
    (∫ _x in (0 : ℝ)..w, Real.sqrt (1 / w) * Real.sqrt (1 / (2 * Real.pi)))
      = Real.sqrt (w / (2 * Real.pi)) := by sorry
