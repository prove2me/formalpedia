-- Prove2me | Theorems.Thm_BookProof_ScalaronWallEsa_testCc_apply
-- name    : BookProof.ScalaronWallEsa.testCc_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:37:28.783502+00:00
-- url     : https://prove2.me/theorems/d22790aa-a8de-44dd-9446-9e076133daed
-- title:
--   The Lean 4 theorem `testCc_apply` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `testCc_apply` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

-- Generated from ChapterScalaronWallEsa.lean — theorem BookProof.ScalaronWallEsa.testCc_apply
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronWallEsa












open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

theorem BookProof.ScalaronWallEsa.testCc_apply {g : ℝ → ℝ} (hg : IsTestFun g) (x : ℝ) :
    ((testCc hg : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = ((g x : ℝ) : ℂ) := by sorry
