-- Prove2me | Theorems.Thm_BookProof_Howland_howland_lintegral_normSq
-- name    : BookProof.Howland.howland_lintegral_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:16:22.816112+00:00
-- url     : https://prove2.me/theorems/b741ebcf-078b-4306-badc-5095b93c5bfa
-- title:
--   `BookProof.Howland.howland_lintegral_normSq` (hU : IsPropagator U) (σ : ℝ) (ψ : ℝ → H) : ∫⁻ t, ENNReal.ofReal (‖howland U σ ψ t‖ ^ 2) = ∫⁻ t, ENNReal.ofReal (‖ψ t‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHowlandAutonomization`.
--
--   `BookProof.Howland.howland_lintegral_normSq` (hU : IsPropagator U) (σ : ℝ) (ψ : ℝ → H) : ∫⁻ t, ENNReal.ofReal (‖howland U σ ψ t‖ ^ 2) = ∫⁻ t, ENNReal.ofReal (‖ψ t‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.Howland.howland_lintegral_normSq`.

-- Generated from ChapterHowlandAutonomization.lean — theorem BookProof.Howland.howland_lintegral_normSq
import Mathlib
import Definitions.Def_ChapterHowlandAutonomization
open BookProof.Howland



open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [NormedAddCommGroup H]
variable {U : ℝ → ℝ → H → H}

theorem BookProof.Howland.howland_lintegral_normSq (hU : IsPropagator U) (σ : ℝ) (ψ : ℝ → H) :
    ∫⁻ t, ENNReal.ofReal (‖howland U σ ψ t‖ ^ 2)
      = ∫⁻ t, ENNReal.ofReal (‖ψ t‖ ^ 2) := by sorry
