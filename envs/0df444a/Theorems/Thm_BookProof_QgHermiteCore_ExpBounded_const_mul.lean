-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_const_mul
-- name    : BookProof.QgHermiteCore.ExpBounded.const_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:18:58.743699+00:00
-- url     : https://prove2.me/theorems/3a73d036-40f5-48ef-bfaf-d6b4dda63914
-- title:
--   {f : E → ℝ} (hf : ExpBounded f) (a : ℝ) : ExpBounded (fun x => a * f x)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.ExpBounded.const_mul` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.ExpBounded.const_mul
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.ExpBounded.const_mul {f : E → ℝ} (hf : ExpBounded f) (a : ℝ) :
    ExpBounded (fun x => a * f x) := by sorry
