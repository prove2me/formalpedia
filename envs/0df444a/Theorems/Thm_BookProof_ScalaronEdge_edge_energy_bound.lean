-- Prove2me | Theorems.Thm_BookProof_ScalaronEdge_edge_energy_bound
-- name    : BookProof.ScalaronEdge.edge_energy_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:12.172557+00:00
-- url     : https://prove2.me/theorems/8f84dff3-4caf-4f55-849b-92609aa7a198
-- title:
--   The Lean 4 theorem `edge_energy_bound` in the `ChapterScalaronEdge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `edge_energy_bound` in the `ChapterScalaronEdge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

-- Generated from ChapterScalaronEdge.lean — theorem BookProof.ScalaronEdge.edge_energy_bound
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

theorem BookProof.ScalaronEdge.edge_energy_bound {A B c : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    (V : ℝ → ℝ) (hVcont : Continuous V) (hVnn : ∀ x, 0 ≤ V x)
    (hVout : ∀ x, x ∉ Set.Icc (-A) B → c ≤ V x)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    min (edgeKinConst A B) (edgeMassConst c) * (∫ x, ‖f x‖ ^ 2)
      ≤ (∫ x, ‖deriv f x‖ ^ 2) + ∫ x, V x * ‖f x‖ ^ 2 := by sorry
