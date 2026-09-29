-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_edgeMassConst_pos
-- name    : BookProof.ScalaronEdge.edgeMassConst_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:32:48.120976+00:00
-- url     : https://prove2.me/theorems/6b3cd119-0c80-4d0d-9c3a-c25d31239a89
-- title:
--   The Lean 4 theorem `edgeMassConst_pos` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `edgeMassConst_pos` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.edgeMassConst_pos
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

theorem BookProof.ScalaronEdge.edgeMassConst_pos {c : ℝ} (hc : 0 < c) : 0 < edgeMassConst c := by sorry
