-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_odeKoop_lintegral_normSq
-- name    : BookProof.OdeUnitaryFlow.odeKoop_lintegral_normSq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:42:09.848976+00:00
-- url     : https://prove2.me/theorems/8ef7794c-db32-4775-92d0-63d93c884321
-- title:
--   `BookProof.OdeUnitaryFlow.odeKoop_lintegral_normSq` (t : ℝ) (ψ : ℝ → ℂ) : ∫⁻ x, ENNReal.ofReal (‖odeKoop t ψ x‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖ψ y‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.odeKoop_lintegral_normSq` (t : ℝ) (ψ : ℝ → ℂ) : ∫⁻ x, ENNReal.ofReal (‖odeKoop t ψ x‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖ψ y‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.odeKoop_lintegral_normSq`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.odeKoop_lintegral_normSq
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.odeKoop_lintegral_normSq (t : ℝ) (ψ : ℝ → ℂ) :
    ∫⁻ x, ENNReal.ofReal (‖odeKoop t ψ x‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖ψ y‖ ^ 2) := by sorry
