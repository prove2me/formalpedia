-- Prove2me | Theorems.Thm_BookProof_ScalaronWallEsa_starobinskyWall_esa
-- name    : BookProof.ScalaronWallEsa.starobinskyWall_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:17:34.825981+00:00
-- url     : https://prove2.me/theorems/92ee2aa0-bc9c-4439-95ad-84fb5378d284
-- title:
--   The Lean 4 theorem `starobinskyWall_esa` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyWall_esa` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

-- Generated from ChapterScalaronWallEsa.lean — theorem BookProof.ScalaronWallEsa.starobinskyWall_esa
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_starobinskyV
open BookProof.ScalaronWallEsa












open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

theorem BookProof.ScalaronWallEsa.starobinskyWall_esa {M alpha : ℝ} (halpha : 0 < alpha) :
    EssentiallySelfAdjointOn (ccDomain ℝ)
      (wallHam (fun phi : ℝ => starobinskyV M alpha phi) (contDiff_starobinskyV M alpha)) := by sorry
