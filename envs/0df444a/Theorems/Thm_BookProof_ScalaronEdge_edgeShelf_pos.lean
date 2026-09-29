-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_edgeShelf_pos
-- name    : BookProof.ScalaronEdge.edgeShelf_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:32:59.568931+00:00
-- url     : https://prove2.me/theorems/a90e5fcc-1c5b-4d49-810b-c06de5a6b9ec
-- title:
--   The Lean 4 theorem `edgeShelf_pos` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `edgeShelf_pos` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.edgeShelf_pos
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

theorem BookProof.ScalaronEdge.edgeShelf_pos (hM : 0 < M) (halpha : 0 < alpha) : 0 < edgeShelf M alpha := by sorry
