-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_edge_normSq_hasDerivAt
-- name    : BookProof.ScalaronEdge.edge_normSq_hasDerivAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:00.761995+00:00
-- url     : https://prove2.me/theorems/acdf9cb9-ce8a-4bcb-8614-dcd4fe0fe3a2
-- title:
--   The Lean 4 theorem `edge_normSq_hasDerivAt` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `edge_normSq_hasDerivAt` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.edge_normSq_hasDerivAt
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

theorem BookProof.ScalaronEdge.edge_normSq_hasDerivAt (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (fun t => ‖f t‖ ^ 2)
      (((starRingEnd ℂ) (deriv f x) * f x + (starRingEnd ℂ) (f x) * deriv f x).re) x := by sorry
