-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_physical_source_compensated_centering
-- name    : AvramDividend.Classical.avram_jump6_B_canonical_physical_source_compensated_centering
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:01:13.459083+00:00
-- url     : https://prove2.me/theorems/60412b36-702c-40e4-a20a-b643b6c6ec1d
-- title:
--   Canonical exact centring of original physical source against generator mesh with deterministic bias
-- statement:
--   For any integrable true source and generator mesh on a probability space, there is a canonical exact decomposition Source=M+Q+bias. The centered remainder M is integrable with precisely zero expectation at each finite physical mesh, and bias is exactly the expected source-minus-generator discrepancy. This separates the algebraic centring, which follows from integrability, from the genuine stochastic obligations that bias tends to zero and the centered remainder converges in L1.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_canonical_physical_source_compensated_centering
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Source Q : ℕ → Ω → ℝ)
    (hSourceI : ∀ j, Integrable (Source j) P)
    (hQI : ∀ j, Integrable (Q j) P) :
    ∃ (bias : ℕ → ℝ) (M : ℕ → Ω → ℝ),
      (∀ j, bias j = ∫ ω, Source j ω - Q j ω ∂P) ∧
      (∀ j ω, Source j ω = M j ω + Q j ω + bias j) ∧
      (∀ j, Integrable (M j) P) ∧
      (∀ j, (∫ ω, M j ω ∂P) = 0) := by sorry
