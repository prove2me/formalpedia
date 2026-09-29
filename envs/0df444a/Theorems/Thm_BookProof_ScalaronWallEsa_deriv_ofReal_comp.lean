-- Prove2me | Theorems.Thm_BookProof_ScalaronWallEsa_deriv_ofReal_comp
-- name    : BookProof.ScalaronWallEsa.deriv_ofReal_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:37:08.366644+00:00
-- url     : https://prove2.me/theorems/761e99f8-a680-4446-9670-78da9e52656a
-- title:
--   The Lean 4 theorem `deriv_ofReal_comp` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `deriv_ofReal_comp` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

-- Generated from ChapterScalaronWallEsa.lean — theorem BookProof.ScalaronWallEsa.deriv_ofReal_comp
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronWallEsa












open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

theorem BookProof.ScalaronWallEsa.deriv_ofReal_comp {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    deriv (fun y => ((g y : ℝ) : ℂ)) = fun x => ((deriv g x : ℝ) : ℂ) := by sorry
