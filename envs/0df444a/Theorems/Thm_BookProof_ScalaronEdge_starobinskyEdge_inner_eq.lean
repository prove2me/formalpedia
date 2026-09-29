-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_starobinskyEdge_inner_eq
-- name    : BookProof.ScalaronEdge.starobinskyEdge_inner_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:16.105017+00:00
-- url     : https://prove2.me/theorems/633c91e9-0339-4a1a-a607-ae4cf827a795
-- title:
--   The Lean 4 theorem `starobinskyEdge_inner_eq` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyEdge_inner_eq` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.starobinskyEdge_inner_eq
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

theorem BookProof.ScalaronEdge.starobinskyEdge_inner_eq (f : ccSchwartz ℝ) :
    (inner ℂ (starobinskyEdgeHam M alpha (ccEquiv ℝ f))
        ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ)) : ℂ)
      = (((∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2)
          + ∫ x, scalV M alpha x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 : ℝ) : ℂ) := by sorry
