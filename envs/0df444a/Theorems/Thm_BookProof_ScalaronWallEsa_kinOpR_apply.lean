-- Prove2me | Theorems.Thm_BookProof_ScalaronWallEsa_kinOpR_apply
-- name    : BookProof.ScalaronWallEsa.kinOpR_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:37:37.480651+00:00
-- url     : https://prove2.me/theorems/75d4c4c4-29ff-4593-a496-317a3cdeb3d5
-- title:
--   The Lean 4 theorem `kinOpR_apply` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `kinOpR_apply` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

-- Generated from ChapterScalaronWallEsa.lean — theorem BookProof.ScalaronWallEsa.kinOpR_apply
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronWallEsa












open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

theorem BookProof.ScalaronWallEsa.kinOpR_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (kinOpR f) x = -deriv (deriv (f : ℝ → ℂ)) x := by sorry
