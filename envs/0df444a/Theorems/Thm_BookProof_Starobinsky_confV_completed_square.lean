-- Prove2me | Theorems.Thm_BookProof_Starobinsky_confV_completed_square
-- name    : BookProof.Starobinsky.confV_completed_square
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:18:08.395141+00:00
-- url     : https://prove2.me/theorems/937f1aed-57ae-451b-b328-f6e1b91145c1
-- title:
--   The Lean 4 theorem `confV_completed_square` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `confV_completed_square` in the `ChapterStarobinskyPotential` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.confV_completed_square
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

theorem BookProof.Starobinsky.confV_completed_square {M alpha : ℝ} (halpha : alpha ≠ 0) (Rc : ℝ) :
    confV M alpha Rc = alpha * (Rc - M ^ 2 / (4 * alpha)) ^ 2 - M ^ 4 / (16 * alpha) := by sorry
