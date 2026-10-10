-- Prove2me | Theorems.Thm_BookProof_Howland_howland_add
-- name    : BookProof.Howland.howland_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:15:54.269749+00:00
-- url     : https://prove2.me/theorems/8242e97d-bf8d-4d90-874d-dce1b2b6335d
-- title:
--   `BookProof.Howland.howland_add` (hU : IsPropagator U) (σ τ : ℝ) (ψ : ℝ → H) : howland U σ (howland U τ ψ) = howland U (σ + τ) ψ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHowlandAutonomization`.
--
--   `BookProof.Howland.howland_add` (hU : IsPropagator U) (σ τ : ℝ) (ψ : ℝ → H) : howland U σ (howland U τ ψ) = howland U (σ + τ) ψ
--
--   Formalization note: Lean 4 identifier `BookProof.Howland.howland_add`.

-- Generated from ChapterHowlandAutonomization.lean — theorem BookProof.Howland.howland_add
import Mathlib
import Definitions.Def_ChapterHowlandAutonomization
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem
open BookProof.Howland



open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [NormedAddCommGroup H]
variable {U : ℝ → ℝ → H → H}

theorem BookProof.Howland.howland_add (hU : IsPropagator U) (σ τ : ℝ) (ψ : ℝ → H) :
    howland U σ (howland U τ ψ) = howland U (σ + τ) ψ := by sorry
