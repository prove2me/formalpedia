-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_dominated_condExp_zero_limit
-- name    : AvramDividend.Classical.avram_ja18_original_dominated_condExp_zero_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:20:18.37153+00:00
-- url     : https://prove2.me/theorems/22922632-3764-4b9e-abc9-bf46713028d7
-- title:
--   Original initial conditional expectation stays zero through dominated almost-sure stopping limits
-- statement:
--   If original adapted stopped rewards along finite clocks converge almost surely to a limiting reward and all rewards share one integrable absolute envelope, their initial conditional expectation remains zero when it is zero for each grid. This is a conditional expectation version of dominated convergence and uses exactly the original initial sigma algebra.
-- source:
--   Genuine analytical limiting child for Open 2d92580d, after Proved original finite-grid optional sampling. Uses pinned Mathlib MeasureTheory.tendsto_condExp_unique.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_dominated_condExp_zero_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (J : ℕ → Ω → ℝ) (Z B : Ω → ℝ)
    (hInt : ∀ k, Integrable (J k) P)
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (Z ω)))
    (hBInt : Integrable B P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ B ω)
    (hZero : ∀ k, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (J k) ω = 0) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P Z ω = 0 := by sorry
