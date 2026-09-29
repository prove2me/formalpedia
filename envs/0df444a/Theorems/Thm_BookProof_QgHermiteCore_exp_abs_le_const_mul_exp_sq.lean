-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_exp_abs_le_const_mul_exp_sq
-- name    : BookProof.QgHermiteCore.exp_abs_le_const_mul_exp_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:28:22.992056+00:00
-- url     : https://prove2.me/theorems/f3815120-2250-4402-9551-46752bb7415c
-- title:
--   (c x : ℝ) : Real.exp (c * |x|) ≤ Real.exp (2 * c ^ 2) * Real.exp (x ^ 2 / 8)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.exp_abs_le_const_mul_exp_sq` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.exp_abs_le_const_mul_exp_sq
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky

theorem BookProof.QgHermiteCore.exp_abs_le_const_mul_exp_sq (c x : ℝ) :
    Real.exp (c * |x|) ≤ Real.exp (2 * c ^ 2) * Real.exp (x ^ 2 / 8) := by sorry
