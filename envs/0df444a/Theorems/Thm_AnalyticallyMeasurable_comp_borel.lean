-- Prove2me | Theorems.Thm_AnalyticallyMeasurable_comp_borel
-- name    : AnalyticallyMeasurable.comp_borel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:00:32.797293+00:00
-- url     : https://prove2.me/theorems/b5ceefe5-2974-5ab5-a104-5af642159a16
-- title:
--   Analytically Measurable: comp borel
-- statement:
--   Composition: analytically measurable after Borel measurable is
--       analytically measurable. Used for the general reduction.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L66-L72
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L66-L72

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem AnalyticallyMeasurable.comp_borel
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z}
    (hf : AnalyticallyMeasurable f)
    (hg : @Measurable Y Z (borel Y) (borel Z) g) :
    AnalyticallyMeasurable (g ∘ f) := by sorry
