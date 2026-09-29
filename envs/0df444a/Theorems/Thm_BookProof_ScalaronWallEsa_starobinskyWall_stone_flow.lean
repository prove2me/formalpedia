-- Prove2me | Theorems.Thm_BookProof_ScalaronWallEsa_starobinskyWall_stone_flow
-- name    : BookProof.ScalaronWallEsa.starobinskyWall_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:17:45.82487+00:00
-- url     : https://prove2.me/theorems/1a7e2545-3a55-4c83-bd00-793299a976f9
-- title:
--   The Lean 4 theorem `starobinskyWall_stone_flow` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyWall_stone_flow` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

-- Generated from ChapterScalaronWallEsa.lean — theorem BookProof.ScalaronWallEsa.starobinskyWall_stone_flow
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

theorem BookProof.ScalaronWallEsa.starobinskyWall_stone_flow {M alpha : ℝ} (halpha : 0 < alpha) :
    ∃ (T : UnboundedSelfAdjoint (Lp ℂ 2 (volume : Measure ℝ)))
      (U : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))),
      IsSelfAdjointExtension
          (wallHam (fun phi : ℝ => starobinskyV M alpha phi)
            (contDiff_starobinskyV M alpha)) T.op ∧
        IsStoneFlow T U := by sorry
