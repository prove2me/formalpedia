-- Prove2me | Theorems.Thm_BookProof_Starobinsky_confV_ge
-- name    : BookProof.Starobinsky.confV_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:14:24.855989+00:00
-- url     : https://prove2.me/theorems/82633658-27be-4af8-a9a8-a6a383881b04
-- title:
--   The Lean 4 theorem `confV_ge` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `confV_ge` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.confV_ge
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.Starobinsky.confV_ge {M alpha : ℝ} (halpha : 0 < alpha) (Rc : ℝ) :
    -(M ^ 4 / (16 * alpha)) ≤ confV M alpha Rc := by sorry
