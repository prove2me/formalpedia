-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_scalaronEdge_friedrichs_gap
-- name    : BookProof.ScalaronEdge.scalaronEdge_friedrichs_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:22.22909+00:00
-- url     : https://prove2.me/theorems/700ce63a-07fc-4df9-b096-37380dbde34e
-- title:
--   The Lean 4 theorem `scalaronEdge_friedrichs_gap` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `scalaronEdge_friedrichs_gap` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.scalaronEdge_friedrichs_gap
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

theorem BookProof.ScalaronEdge.scalaronEdge_friedrichs_gap (hM : 0 < M) (halpha : 0 < alpha) (c : ℝ) (hc : 0 < c)
    (hcs : c < edgeShelf M alpha) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∃ (Dom : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)))
      (A : Dom →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
      (S : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)),
      IsPositiveSelfAdjointExtension (starobinskyEdgeHam M alpha) A ∧ IsShiftInvert A 1 S ∧
        IsSelfAdjoint S ∧ (∀ y : Dom, E₀ * ‖(y : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2
          ≤ quadForm A y) := by sorry
