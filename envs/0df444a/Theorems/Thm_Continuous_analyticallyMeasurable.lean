-- Prove2me | Theorems.Thm_Continuous_analyticallyMeasurable
-- name    : Continuous.analyticallyMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:00:49.235859+00:00
-- url     : https://prove2.me/theorems/813c2149-e8e0-5691-ace5-94d8d8c8013e
-- title:
--   Continuous: analytically Measurable
-- statement:
--   Continuous functions between Polish spaces are analytically measurable.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L53-L62
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L53-L62

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem Continuous.analyticallyMeasurable
    [PolishSpace X]
    {Y : Type*} [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : AnalyticallyMeasurable f := by sorry
