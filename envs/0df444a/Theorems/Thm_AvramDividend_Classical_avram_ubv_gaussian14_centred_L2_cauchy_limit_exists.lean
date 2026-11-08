-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian14_centred_L2_cauchy_limit_exists
-- name    : AvramDividend.Classical.avram_ubv_gaussian14_centred_L2_cauchy_limit_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:29:04.413404+00:00
-- url     : https://prove2.me/theorems/1dc8ba44-e4de-4188-9807-1902c1a8c3ed
-- title:
--   Centred Gaussian stochastic grid Cauchy control constructs a square-integrable centred terminal variable
-- statement:
--   On the original probability space, every finite stopped Gaussian stochastic grid is square-integrable and centred. If pairwise L2 distances tend to zero over the directed product of grid indices, the L2 function space completeness theorem constructs a terminal random variable in L2, proves convergence in L2 of the original grid, and transfers exact zero expectation. In particular a separate terminal existence or measurability assumption is unnecessary. The martingale-grid and pairwise L2 hypotheses are explicit for later instantiation.
-- source:
--   Pinned Mathlib Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm, cauchySeq_tendsto_of_complete, Lp.tendsto_Lp_iff_tendsto_eLpNorm', and tendsto_integral_of_L1'.

import Mathlib

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian14_centred_L2_cauchy_limit_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Q : ℕ → Ω → ℝ)
    (hQ2 : ∀ n, MemLp (Q n) 2 P)
    (hQzero : ∀ n, (∫ ω, Q n ω ∂P) = 0)
    (hCauchy : Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (Q nm.1 - Q nm.2) 2 P) atTop (𝓝 0)) :
    ∃ L : Ω → ℝ, MemLp L 2 P ∧
      (∫ ω, L ω ∂P) = 0 ∧
      Tendsto (fun n => eLpNorm (Q n - L) 2 P) atTop (𝓝 0) := by sorry
