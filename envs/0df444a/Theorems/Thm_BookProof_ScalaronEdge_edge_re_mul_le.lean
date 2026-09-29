-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_edge_re_mul_le
-- name    : BookProof.ScalaronEdge.edge_re_mul_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:08.032178+00:00
-- url     : https://prove2.me/theorems/a68f181e-260d-429a-bc87-cf179c93e019
-- title:
--   The Lean 4 theorem `edge_re_mul_le` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `edge_re_mul_le` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.edge_re_mul_le
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

theorem BookProof.ScalaronEdge.edge_re_mul_le (z w : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ((starRingEnd ℂ) w * z + (starRingEnd ℂ) z * w).re ≤ δ * ‖z‖ ^ 2 + δ⁻¹ * ‖w‖ ^ 2 := by sorry
