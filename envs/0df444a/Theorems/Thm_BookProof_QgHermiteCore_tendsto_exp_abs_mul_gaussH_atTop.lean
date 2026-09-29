-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_tendsto_exp_abs_mul_gaussH_atTop
-- name    : BookProof.QgHermiteCore.tendsto_exp_abs_mul_gaussH_atTop
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:28:03.791593+00:00
-- url     : https://prove2.me/theorems/da55f99d-5028-4b28-a189-b9306fa87a21
-- title:
--   (c : ℝ) : Tendsto (fun x : ℝ => Real.exp (c * |x|) * gaussH x) atTop (𝓝 0)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.tendsto_exp_abs_mul_gaussH_atTop` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.tendsto_exp_abs_mul_gaussH_atTop
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky

theorem BookProof.QgHermiteCore.tendsto_exp_abs_mul_gaussH_atTop (c : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (c * |x|) * gaussH x) atTop (𝓝 0) := by sorry
