-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_lintegral_comp_invMap
-- name    : BookProof.OdeUnitaryFlow.lintegral_comp_invMap
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:03:42.707788+00:00
-- url     : https://prove2.me/theorems/54abc2bb-e133-411e-a1a9-2fefa13f7bed
-- title:
--   `BookProof.OdeUnitaryFlow.lintegral_comp_invMap` (g : ℝ → ℝ≥0∞) : ∫⁻ x, ENNReal.ofReal ((x ^ 2)⁻¹) * g (invMap x) = ∫⁻ y, g y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.lintegral_comp_invMap` (g : ℝ → ℝ≥0∞) : ∫⁻ x, ENNReal.ofReal ((x ^ 2)⁻¹) * g (invMap x) = ∫⁻ y, g y
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.lintegral_comp_invMap`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.lintegral_comp_invMap
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.lintegral_comp_invMap (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal ((x ^ 2)⁻¹) * g (invMap x) = ∫⁻ y, g y := by sorry
