-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_chartW_lintegral_normSq
-- name    : BookProof.OdeUnitaryFlow.chartW_lintegral_normSq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:03:40.91195+00:00
-- url     : https://prove2.me/theorems/7c7f538c-41dd-44cd-b76c-2de63f97894e
-- title:
--   `BookProof.OdeUnitaryFlow.chartW_lintegral_normSq` (ψ : ℝ → ℂ) : ∫⁻ x, ENNReal.ofReal (‖chartW ψ x‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖ψ y‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.chartW_lintegral_normSq` (ψ : ℝ → ℂ) : ∫⁻ x, ENNReal.ofReal (‖chartW ψ x‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖ψ y‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.chartW_lintegral_normSq`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.chartW_lintegral_normSq
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.chartW_lintegral_normSq (ψ : ℝ → ℂ) :
    ∫⁻ x, ENNReal.ofReal (‖chartW ψ x‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖ψ y‖ ^ 2) := by sorry
