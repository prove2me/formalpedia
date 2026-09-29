-- Prove2me | Theorems.Thm_BookProof_ScalaronWallEsa_wallHam_symmetricOn
-- name    : BookProof.ScalaronWallEsa.wallHam_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:41:14.716496+00:00
-- url     : https://prove2.me/theorems/e1b3a639-5a29-4315-b4fe-93b9f1bfe17c
-- title:
--   The Lean 4 theorem `wallHam_symmetricOn` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wallHam_symmetricOn` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

-- Generated from ChapterScalaronWallEsa.lean — theorem BookProof.ScalaronWallEsa.wallHam_symmetricOn
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronWallEsa












open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

theorem BookProof.ScalaronWallEsa.wallHam_symmetricOn (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    SymmetricOn (ccDomain ℝ) (wallHam V hV) := by sorry
