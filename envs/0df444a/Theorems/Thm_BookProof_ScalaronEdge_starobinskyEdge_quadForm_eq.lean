-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_starobinskyEdge_quadForm_eq
-- name    : BookProof.ScalaronEdge.starobinskyEdge_quadForm_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:57.592323+00:00
-- url     : https://prove2.me/theorems/a84af621-f362-4698-9832-7c2d7a3c43ac
-- title:
--   The Lean 4 theorem `starobinskyEdge_quadForm_eq` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyEdge_quadForm_eq` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.starobinskyEdge_quadForm_eq
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

theorem BookProof.ScalaronEdge.starobinskyEdge_quadForm_eq (f : ccSchwartz ℝ) :
    quadForm (starobinskyEdgeHam M alpha) (ccEquiv ℝ f)
      = (∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2)
        + ∫ x, scalV M alpha x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by sorry
