-- Prove2me | Theorems.Thm_Continuous_borel_borel_measurable
-- name    : Continuous.borel_borel_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:00:40.779255+00:00
-- url     : https://prove2.me/theorems/8d79c3f9-7b5b-5429-90fa-9cb5c3c4c92d
-- title:
--   Continuous: borel borel measurable
-- statement:
--   Continuous functions are Borel-Borel measurable.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L75-L84
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L75-L84

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem Continuous.borel_borel_measurable
    {Y : Type*} [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) :
    @Measurable X Y (borel X) (borel Y) f := by sorry
