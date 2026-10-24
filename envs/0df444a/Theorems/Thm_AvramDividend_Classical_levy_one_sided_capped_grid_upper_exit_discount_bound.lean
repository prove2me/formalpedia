-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_one_sided_capped_grid_upper_exit_discount_bound
-- name    : AvramDividend.Classical.levy_one_sided_capped_grid_upper_exit_discount_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:16:19.726752+00:00
-- url     : https://prove2.me/theorems/79ea4eef-a91a-414b-99fb-5f4e4668e8e1
-- title:
--   One-sided capped uniform-clock Lévy upper-exit discounted exponential bound without an auxiliary lower boundary
-- statement:
--   For a spectrally negative Lévy process and an adapted monotone sampling clock, θ≥0 with ψ(θ)≥0, an upper level and finite horizon m, let K be the bounded first index where X(clock k)>upper, with terminal cap m. Show E[exp(−ψ(θ)clock K)1_{X(clock K)>upper}]≤exp(−θ upper) with **no lower barrier**. Existing Proved levy_grid_upper_exit_discount_bound_complete gives the same bound with arbitrary lower barrier −n in its stopping test. Use the independently proved finite-observation lower-barrier exhaustion and bounded hitting-time equality to obtain K_n(ω)=Kupper(ω) eventually for each finite grid path. Convert the finite two-sided real expected bounds to nonnegative ENNReal integrals, use the Fatou bound proved in finite_grid_upper_reward_bound_of_receding_lower_barrier, and convert the resulting positive expected upper bound back to reals. The measure is probabilistic by X.isProbability. This is the exact finite-grid missing stochastic theorem needed before the full one-sided q-discounted first-passage Esscher bound. Avoid all Standing hypotheses and circular imports.
-- source:
--   Prove2Me levy_grid_upper_exit_discount_bound_complete (Proved), finite-grid lower-barrier exhaustion, first hittingBtwn congruence and grid_exit_real_to_lintegral_limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_one_sided_capped_grid_upper_exit_discount_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 ≤ X.ψ θ)
    (upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => X.X (clock k) ω - upper)
      (Ioi (0 : ℝ)) 0 m ω) :
    (∫ ω, {ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
      (fun z => Real.exp (-((clock (K z)) : ℝ) * X.ψ θ)) ω ∂P) ≤
      Real.exp (-θ * upper) := by sorry
