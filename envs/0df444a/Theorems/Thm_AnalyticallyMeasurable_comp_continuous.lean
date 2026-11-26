-- Prove2me | Theorems.Thm_AnalyticallyMeasurable_comp_continuous
-- name    : AnalyticallyMeasurable.comp_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:00.384291+00:00
-- url     : https://prove2.me/theorems/3ced4fa2-9472-48bd-af0c-f0b5f83a475d
-- title:
--   Analytically Measurable: comp continuous
-- statement:
--   Composition of analytically measurable with continuous is
--       analytically measurable.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L88-L93
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L88-L93

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem AnalyticallyMeasurable.comp_continuous
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z}
    (hf : AnalyticallyMeasurable f) (hg : Continuous g) :
    AnalyticallyMeasurable (g ∘ f) := by sorry
