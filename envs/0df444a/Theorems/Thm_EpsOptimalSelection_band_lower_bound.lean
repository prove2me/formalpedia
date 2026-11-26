-- Prove2me | Theorems.Thm_EpsOptimalSelection_band_lower_bound
-- name    : EpsOptimalSelection.band_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:57.273248+00:00
-- url     : https://prove2.me/theorems/e5758dbf-f032-4293-8b18-4e425fa154a6
-- title:
--   Eps Optimal Selection: band lower bound
-- statement:
--   Failure of all band predicates below `m + 1` bounds the value from
--       below by the `m`-th band's lower edge.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L123-L128
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L123-L128

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

theorem EpsOptimalSelection.band_lower_bound {ε' v : ℝ≥0∞} {m : ℕ}
    (hmin : ∀ j, j < m + 1 → ¬ bandPred ε' j v) :
    ((m : ℕ) : ℝ≥0∞) * ε' ≤ v := by sorry
