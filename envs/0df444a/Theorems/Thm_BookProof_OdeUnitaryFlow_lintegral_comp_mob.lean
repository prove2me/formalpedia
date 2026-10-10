-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_lintegral_comp_mob
-- name    : BookProof.OdeUnitaryFlow.lintegral_comp_mob
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:43:00.958202+00:00
-- url     : https://prove2.me/theorems/277042aa-7863-4bf2-84eb-910b1253d82b
-- title:
--   `BookProof.OdeUnitaryFlow.lintegral_comp_mob` (t : ℝ) (g : ℝ → ℝ≥0∞) : ∫⁻ x, ENNReal.ofReal ((1 + t * x) ^ 2)⁻¹ * g (mob t x) = ∫⁻ y, g y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.lintegral_comp_mob` (t : ℝ) (g : ℝ → ℝ≥0∞) : ∫⁻ x, ENNReal.ofReal ((1 + t * x) ^ 2)⁻¹ * g (mob t x) = ∫⁻ y, g y
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.lintegral_comp_mob`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.lintegral_comp_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.lintegral_comp_mob (t : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal ((1 + t * x) ^ 2)⁻¹ * g (mob t x) = ∫⁻ y, g y := by sorry
