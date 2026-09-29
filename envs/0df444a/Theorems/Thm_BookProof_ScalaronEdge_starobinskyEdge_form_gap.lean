-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_starobinskyEdge_form_gap
-- name    : BookProof.ScalaronEdge.starobinskyEdge_form_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:51.459766+00:00
-- url     : https://prove2.me/theorems/1162d40c-59c9-4727-ad90-f6d434c2a520
-- title:
--   The Lean 4 theorem `starobinskyEdge_form_gap` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyEdge_form_gap` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.starobinskyEdge_form_gap
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

theorem BookProof.ScalaronEdge.starobinskyEdge_form_gap (hM : 0 < M) (halpha : 0 < alpha) (c : ℝ) (hc : 0 < c)
    (hcs : c < edgeShelf M alpha) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ ψ : ccDomain ℝ,
      E₀ * ‖(ψ : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2
        ≤ quadForm (starobinskyEdgeHam M alpha) ψ := by sorry
