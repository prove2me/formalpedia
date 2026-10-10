-- Prove2me | Theorems.Thm_BookProof_Howland_howland_neg
-- name    : BookProof.Howland.howland_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:16:01.859991+00:00
-- url     : https://prove2.me/theorems/35db3b6b-40f7-4997-ad67-a8f8b049178a
-- title:
--   `BookProof.Howland.howland_neg` (hU : IsPropagator U) (σ : ℝ) (ψ : ℝ → H) : howland U (-σ) (howland U σ ψ) = ψ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHowlandAutonomization`.
--
--   `BookProof.Howland.howland_neg` (hU : IsPropagator U) (σ : ℝ) (ψ : ℝ → H) : howland U (-σ) (howland U σ ψ) = ψ
--
--   Formalization note: Lean 4 identifier `BookProof.Howland.howland_neg`.

-- Generated from ChapterHowlandAutonomization.lean — theorem BookProof.Howland.howland_neg
import Mathlib
import Definitions.Def_ChapterHowlandAutonomization
open BookProof.Howland



open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [NormedAddCommGroup H]
variable {U : ℝ → ℝ → H → H}

theorem BookProof.Howland.howland_neg (hU : IsPropagator U) (σ : ℝ) (ψ : ℝ → H) :
    howland U (-σ) (howland U σ ψ) = ψ := by sorry
