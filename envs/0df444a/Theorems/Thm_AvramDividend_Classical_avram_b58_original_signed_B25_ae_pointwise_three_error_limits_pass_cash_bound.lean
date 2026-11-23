-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b58_original_signed_B25_ae_pointwise_three_error_limits_pass_cash_bound
-- name    : AvramDividend.Classical.avram_b58_original_signed_B25_ae_pointwise_three_error_limits_pass_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:49:58.655206+00:00
-- url     : https://prove2.me/theorems/ebede0f8-8612-42cd-a4ef-b9c5713d5527
-- title:
--   Exact B25 signed physical cash inequality passes to almost-sure limit with merely pointwise-vanishing mesh errors, without assuming false L1 error convergence
-- statement:
--   The actual original B25 source provides almost-sure convergence of both physical noise-grid sums G,J and the signed error E to zero, while its positive-clock cash inequality holds for every mesh index. On their common full-measure set, passing the real scalar inequality to the pointwise limits gives F<=w(x)+MG+MJ. This removes any extra L1 assumption on E, which the original B25 never supplies, and is essential for a mathematically source-faithful conditional counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b58_original_signed_B25_ae_pointwise_three_error_limits_pass_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F MG MJ : Ω → ℝ) (b : ℝ)
    (G J E : ℕ → Ω → ℝ)
    (hGlim : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hJlim : ∀ᵐ ω ∂P,
      Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω)))
    (hElim : ∀ᵐ ω ∂P,
      Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)))
    (hCashAll : ∀ᵐ ω ∂P, ∀ k,
      F ω ≤ b + G k ω + J k ω + E k ω) :
    ∀ᵐ ω ∂P, F ω ≤ b + MG ω + MJ ω := by sorry
