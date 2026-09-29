-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_starobinskyV_lt_shelf_bounded
-- name    : BookProof.ScalaronEdge.starobinskyV_lt_shelf_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:32:56.933102+00:00
-- url     : https://prove2.me/theorems/a15127c7-c305-4142-b63f-9dc4ae2ba929
-- title:
--   The Lean 4 theorem `starobinskyV_lt_shelf_bounded` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyV_lt_shelf_bounded` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.starobinskyV_lt_shelf_bounded
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

theorem BookProof.ScalaronEdge.starobinskyV_lt_shelf_bounded (hM : 0 < M) (halpha : 0 < alpha) (c : ℝ) (hc : 0 < c)
    (hcs : c < edgeShelf M alpha) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ x : ℝ, scalV M alpha x < c → x ∈ Set.Icc (-A) B := by sorry
