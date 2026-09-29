-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_exp_abs_mul_gaussH_le
-- name    : BookProof.QgHermiteCore.exp_abs_mul_gaussH_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:45:40.224378+00:00
-- url     : https://prove2.me/theorems/9d1064b1-f6d5-409e-8a7e-1958c607358b
-- title:
--   (c x : ℝ) : Real.exp (c * |x|) * gaussH x ≤ Real.exp (2 * c ^ 2) * Real.exp (-x ^ 2 / 8)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.exp_abs_mul_gaussH_le` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.exp_abs_mul_gaussH_le
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky

theorem BookProof.QgHermiteCore.exp_abs_mul_gaussH_le (c x : ℝ) :
    Real.exp (c * |x|) * gaussH x ≤ Real.exp (2 * c ^ 2) * Real.exp (-x ^ 2 / 8) := by sorry
