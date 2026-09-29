-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_edge_sup_sq_le
-- name    : BookProof.ScalaronEdge.edge_sup_sq_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:30.633027+00:00
-- url     : https://prove2.me/theorems/8899edcc-3250-4317-bcf6-9b210485c6d7
-- title:
--   The Lean 4 theorem `edge_sup_sq_le` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `edge_sup_sq_le` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.edge_sup_sq_le
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

theorem BookProof.ScalaronEdge.edge_sup_sq_le (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ‖f x‖ ^ 2 ≤ ∫ t, (δ * ‖f t‖ ^ 2 + δ⁻¹ * ‖deriv f t‖ ^ 2) := by sorry
