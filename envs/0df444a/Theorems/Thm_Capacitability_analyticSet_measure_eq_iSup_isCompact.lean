-- Prove2me | Theorems.Thm_Capacitability_analyticSet_measure_eq_iSup_isCompact
-- name    : Capacitability.analyticSet_measure_eq_iSup_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:44.225268+00:00
-- url     : https://prove2.me/theorems/f91ac6d8-744e-5374-9b40-e39631ef2b9d
-- title:
--   Capacitability: analytic Set measure eq i Sup is Compact
-- statement:
--   **Choquet capacitability, measure case** (Kechris, *Classical Descriptive Set Theory*,
--   Theorem 30.13 instantiated at the capacity `γ = μ*` of Example 30.B.1; Bertsekas–Shreve,
--   *Stochastic Optimal Control: The Discrete Time Case*, Proposition 7.42).
--
--   For a finite Borel measure `μ` on a Polish space `X`, the outer measure of an analytic set
--   `A ⊆ X` is the supremum of the measures of the compact subsets of `A`.  `A` is not assumed
--   measurable.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/SolutionCapacitability.lean#L75-L81
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/SolutionCapacitability.lean#L75-L81

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_SolutionCapacitability
set_option autoImplicit false
open MeasureTheory
open Capacitability

theorem Capacitability.analyticSet_measure_eq_iSup_isCompact
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    μ A = ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), μ K := by sorry
