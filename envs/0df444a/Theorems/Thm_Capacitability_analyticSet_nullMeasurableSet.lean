-- Prove2me | Theorems.Thm_Capacitability_analyticSet_nullMeasurableSet
-- name    : Capacitability.analyticSet_nullMeasurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:49.965972+00:00
-- url     : https://prove2.me/theorems/e20e034f-2179-4978-8ad0-8a64edd90e22
-- title:
--   Capacitability: analytic Set null Measurable Set
-- statement:
--   **Analytic sets are universally measurable** (Lusin; Kechris, *Classical Descriptive Set
--   Theory*, Exercise 30.11 combined with Theorem 30.13; Bertsekas–Shreve, *Stochastic Optimal
--   Control: The Discrete Time Case*, Corollary 7.42.1 of Proposition 7.42).
--
--   An analytic subset of a Polish space is null-measurable with respect to every finite Borel
--   measure: it differs from a Borel set by a null set.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/SolutionCapacitability.lean#L89-L95
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/SolutionCapacitability.lean#L89-L95

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_SolutionCapacitability
set_option autoImplicit false
open MeasureTheory
open Capacitability

theorem Capacitability.analyticSet_nullMeasurableSet
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet A μ := by sorry
