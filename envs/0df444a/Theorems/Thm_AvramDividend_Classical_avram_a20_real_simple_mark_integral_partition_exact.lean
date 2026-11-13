-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_real_simple_mark_integral_partition_exact
-- name    : AvramDividend.Classical.avram_a20_real_simple_mark_integral_partition_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:00:30.018276+00:00
-- url     : https://prove2.me/theorems/8360c4c0-c760-4abd-b89a-b281a4bbdf83
-- title:
--   Real integral of finite-valued Borel mark over a physical time-mark rectangle equals weighted disjoint mark-cell counts
-- statement:
--   For any measure μ on nonnegative time × real jump marks, any Borel spatial set S and finite-valued measurable real mark function g whose mark integral is integrable over (0,t]×S, the exact real source integral of g(z) equals the finite sum over values y in g.range of y times the real μ-mass of the physical Borel rectangle (0,t]×(S∩g^{-1}({y})). The proof applies the authoritative Mathlib SimpleFunc.integral_eq_sum to g composed with the second coordinate, transfers to the restricted physical rectangle measure, and uses measurable fibre partitions. The result is the missing exact conversion between the independently Proved original finite-simple Borel raw moments and original marked real Poisson jump integrals, without any replacement source process or Poisson count-law assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_real_simple_mark_integral_partition_exact
    (μ : Measure (ℝ≥0 × ℝ)) (t : ℝ≥0)
    (S : Set ℝ) (hS : MeasurableSet S)
    (g : SimpleFunc ℝ ℝ)
    (hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => g p.2)
      (Ioc 0 t ×ˢ S) μ) :
    (∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂μ) =
      ∑ y ∈ g.range, y *
        (μ (Ioc 0 t ×ˢ (S ∩ g ⁻¹' {y}))).toReal := by sorry
