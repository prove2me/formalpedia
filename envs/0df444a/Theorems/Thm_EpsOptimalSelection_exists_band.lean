-- Prove2me | Theorems.Thm_EpsOptimalSelection_exists_band
-- name    : EpsOptimalSelection.exists_band
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:50.537635+00:00
-- url     : https://prove2.me/theorems/f5984c35-e904-510a-9d6b-8ca573f2682d
-- title:
--   Eps Optimal Selection: exists band
-- statement:
--   Every value lies in some band (Archimedean property of the grid).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L109-L119
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L109-L119

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
open EpsOptimalSelection

theorem EpsOptimalSelection.exists_band {ε' : ℝ≥0∞} (hε'0 : 0 < ε') (hε'top : ε' ≠ ∞)
    (v : ℝ≥0∞) : ∃ m : ℕ, bandPred ε' m v := by sorry
