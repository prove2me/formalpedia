-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_starobinskyEdge_self_inner
-- name    : BookProof.ScalaronEdge.starobinskyEdge_self_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:27.678759+00:00
-- url     : https://prove2.me/theorems/5adbd7f6-9cf6-4804-8a6e-a4867119e746
-- title:
--   The Lean 4 theorem `starobinskyEdge_self_inner` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyEdge_self_inner` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.starobinskyEdge_self_inner
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

theorem BookProof.ScalaronEdge.starobinskyEdge_self_inner (f : ccSchwartz ℝ) :
    (inner ℂ ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ))
        ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ)) : ℂ)
      = ((∫ x, ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 : ℝ) : ℂ) := by sorry
