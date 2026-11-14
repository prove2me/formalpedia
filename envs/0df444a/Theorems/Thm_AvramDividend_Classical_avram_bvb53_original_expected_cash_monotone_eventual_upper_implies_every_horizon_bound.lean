-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb53_original_expected_cash_monotone_eventual_upper_implies_every_horizon_bound
-- name    : AvramDividend.Classical.avram_bvb53_original_expected_cash_monotone_eventual_upper_implies_every_horizon_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:03:55.863605+00:00
-- url     : https://prove2.me/theorems/1d961b00-1420-4ab5-bf47-366073d559e6
-- title:
--   Integrable monotone original-clock cash sequence with eventually epsilon-accurate expected upper bound satisfies every fixed strict-horizon expected bound
-- statement:
--   For any finite original probability-based sequence of integrable real cash rewards monotonically increasing a.e., if for every positive epsilon the expectations are eventually bounded above by the same candidate initial value plus epsilon, then the expected cash at every finite row is bounded by that initial value. The proof uses a max-index along the original sequence, integrability-based monotonicity of expectation and a half-gap contradiction. Applied with Proved original BV-B47 fixed-terminal cash monotonicity c5eeb765, this supplies a sound same-clock expectation-level route to topcap c1b8325c, avoiding its analytically suspect pathwise premature compensated-jump truncation 28336ae5.
-- source:
--   Proved original cash+true terminal monotonicity c5eeb765 and elementary integral_mono_ae.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- An asymptotic one-clock expected cash upper bound suffices for each
earlier strictly stopped horizon when actual cash is increasing a.e. -/

theorem AvramDividend.Classical.avram_bvb53_original_expected_cash_monotone_eventual_upper_implies_every_horizon_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (w : ℝ)
    (hInt : ∀ n, Integrable (F n) P)
    (hMono : ∀ n m, n ≤ m → ∀ᵐ ω ∂P, F n ω ≤ F m ω)
    (hUpper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in (atTop : Filter ℕ), (∫ ω, F m ω ∂P) ≤ w + ε) :
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w := by sorry
