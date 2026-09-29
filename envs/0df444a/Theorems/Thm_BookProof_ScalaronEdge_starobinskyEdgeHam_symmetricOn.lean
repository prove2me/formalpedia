-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_starobinskyEdgeHam_symmetricOn
-- name    : BookProof.ScalaronEdge.starobinskyEdgeHam_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:32:43.133387+00:00
-- url     : https://prove2.me/theorems/9f4300cf-39dd-48aa-a1d5-2c64ed4109b9
-- title:
--   The Lean 4 theorem `starobinskyEdgeHam_symmetricOn` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyEdgeHam_symmetricOn` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.starobinskyEdgeHam_symmetricOn
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

theorem BookProof.ScalaronEdge.starobinskyEdgeHam_symmetricOn :
    SymmetricOn (ccDomain ℝ) (starobinskyEdgeHam M alpha) := by sorry
