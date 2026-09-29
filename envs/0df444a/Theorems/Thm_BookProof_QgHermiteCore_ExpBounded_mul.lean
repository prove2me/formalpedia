-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_mul
-- name    : BookProof.QgHermiteCore.ExpBounded.mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:43:41.13056+00:00
-- url     : https://prove2.me/theorems/053a970a-90e5-4fc2-ba8f-aee9acb0707a
-- title:
--   {f g : E → ℝ} (hf : ExpBounded f) (hg : ExpBounded g) : ExpBounded (fun x => f x * g x)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.ExpBounded.mul` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.ExpBounded.mul
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.ExpBounded.mul {f g : E → ℝ} (hf : ExpBounded f) (hg : ExpBounded g) :
    ExpBounded (fun x => f x * g x) := by sorry
