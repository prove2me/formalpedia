-- Prove2me | Theorems.Thm_BookProof_ScalaronWallEsa_ode_solution_eq_zero
-- name    : BookProof.ScalaronWallEsa.ode_solution_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:41:01.470423+00:00
-- url     : https://prove2.me/theorems/1d9687b7-d3f5-4e9d-a52d-27dd0a78229d
-- title:
--   The Lean 4 theorem `ode_solution_eq_zero` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ode_solution_eq_zero` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

-- Generated from ChapterScalaronWallEsa.lean — theorem BookProof.ScalaronWallEsa.ode_solution_eq_zero
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronWallEsa












open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

theorem BookProof.ScalaronWallEsa.ode_solution_eq_zero {V : ℝ → ℝ} (hVnn : ∀ x, 0 ≤ V x) {z : ℂ} (hz : z.re = 0)
    {W W' : ℝ → ℂ} (hW : ∀ x, HasDerivAt W (W' x) x)
    (hW' : ∀ x, HasDerivAt W' ((((V x : ℝ) : ℂ) - z) * W x) x)
    (hint : Integrable (fun x => ‖W x‖ ^ 2) volume) :
    ∀ x, W x = 0 := by sorry
