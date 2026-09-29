-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_scalV_nonneg
-- name    : BookProof.ScalaronEdge.scalV_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:13.012799+00:00
-- url     : https://prove2.me/theorems/766ef68f-206d-4f99-9c73-4dd64a42f4b5
-- title:
--   The Lean 4 theorem `scalV_nonneg` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `scalV_nonneg` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.scalV_nonneg
import Mathlib
import Definitions.Def_ChapterScalaronEdge
open BookProof.ScalaronEdge









open Complex Real MeasureTheory Function SchwartzMap ComplexOrder
open BookProof.Starobinsky
open BookProof.ScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.FarisLavine
open BookProof.WallEsaSemibounded
open BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert



variable (M alpha : ℝ)

theorem BookProof.ScalaronEdge.scalV_nonneg (halpha : 0 < alpha) (x : ℝ) : 0 ≤ scalV M alpha x := by sorry
