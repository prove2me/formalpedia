-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_starobinskyEdge_quadForm
-- name    : BookProof.ScalaronEdge.starobinskyEdge_quadForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:01.669466+00:00
-- url     : https://prove2.me/theorems/b6b83dfe-057a-4258-8ea1-619063c2b0d6
-- title:
--   The Lean 4 theorem `starobinskyEdge_quadForm` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyEdge_quadForm` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.starobinskyEdge_quadForm
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

theorem BookProof.ScalaronEdge.starobinskyEdge_quadForm (hM : 0 < M) (halpha : 0 < alpha) (c : ℝ) (hc : 0 < c)
    (hcs : c < edgeShelf M alpha) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ ψ : ccDomain ℝ,
      (inner ℂ (starobinskyEdgeHam M alpha ψ)
          ((ψ : Lp ℂ 2 (volume : Measure ℝ))) : ℂ)
        ≥ (E₀ : ℂ) * inner ℂ ((ψ : Lp ℂ 2 (volume : Measure ℝ)))
            ((ψ : Lp ℂ 2 (volume : Measure ℝ))) := by sorry
