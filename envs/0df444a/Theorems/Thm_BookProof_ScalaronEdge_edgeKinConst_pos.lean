-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_edgeKinConst_pos
-- name    : BookProof.ScalaronEdge.edgeKinConst_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:32:33.567812+00:00
-- url     : https://prove2.me/theorems/70314dd2-5c2a-4d95-a2ca-b7ec780197dc
-- title:
--   The Lean 4 theorem `edgeKinConst_pos` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `edgeKinConst_pos` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.edgeKinConst_pos
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

theorem BookProof.ScalaronEdge.edgeKinConst_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : 0 < edgeKinConst A B := by sorry
