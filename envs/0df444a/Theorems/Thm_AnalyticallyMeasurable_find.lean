-- Prove2me | Theorems.Thm_AnalyticallyMeasurable_find
-- name    : AnalyticallyMeasurable.find
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:57.729431+00:00
-- url     : https://prove2.me/theorems/b59f9563-7b9b-420c-ba14-f82a2130d31c
-- title:
--   Analytically Measurable: find
-- statement:
--   **Countable σ(Σ¹₁)-piecewise gluing.** Steering among countably many
--       analytically measurable maps through the least index satisfying
--       σ(Σ¹₁)-measurable predicates yields an analytically measurable map:
--       Mathlib's `Measurable.find` instantiated at
--       `analyticMeasurableSpace`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L86-L94
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L86-L94

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]

theorem AnalyticallyMeasurable.find
    {ψ : ℕ → H → E} (hψ : ∀ m, AnalyticallyMeasurable (ψ m))
    {p : ℕ → H → Prop} [∀ m, DecidablePred (p m)]
    (hp : ∀ m, @MeasurableSet H (analyticMeasurableSpace H) {h | p m h})
    (hex : ∀ h, ∃ m, p m h) :
    AnalyticallyMeasurable (fun h => ψ (Nat.find (hex h)) h) := by sorry
