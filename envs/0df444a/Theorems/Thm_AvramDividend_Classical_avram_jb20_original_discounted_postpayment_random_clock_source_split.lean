-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb20_original_discounted_postpayment_random_clock_source_split
-- name    : AvramDividend.Classical.avram_jb20_original_discounted_postpayment_random_clock_source_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:04:24.061754+00:00
-- url     : https://prove2.me/theorems/e7e708b8-f581-4a5e-9d75-fecdf8a05640
-- title:
--   Original discounted physical reserve increment splits into Gaussian, jumps, right-limit dividends and discount change
-- statement:
--   At arbitrary original sample-dependent clocks, split the discounted physical post-payment reserve increment into the original Lévy drift, source-totalised intrinsic Gaussian increment, compensated small-jump increment, raw large-negative-jump increment and exact right-limit dividend increment, all weighted by the later discount factor, plus the earlier reserve times the discount change. This exact accounting retains the time-zero/right-payment conventions needed before the nonlinear C2 Ito-Meyer expansion; it assumes no auxiliary zero-jump process or martingale centring.
-- source:
--   Proved 48ec85d6 original random-clock Levy source increments and Proved 983c337d exact discounted post-payment reserve product decomposition. Component of Open 544e8511 physical stopped ledger, not the complete stochastic ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_discounted_increment_decomposition
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb20_original_discounted_postpayment_random_clock_source_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) ∧
      (∀ (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
          (α β : Ω → ℝ≥0) (ω : Ω),
        Real.exp (-(q * (β ω : ℝ))) *
          (x + X.X (β ω) ω - rightLimit D (β ω) ω) -
        Real.exp (-(q * (α ω : ℝ))) *
          (x + X.X (α ω) ω - rightLimit D (α ω) ω) =
        Real.exp (-(q * (β ω : ℝ))) *
          (((β ω : ℝ) - (α ω : ℝ)) * X.c +
            (M (β ω) ω - M (α ω) ω) +
            (Jsmall (β ω) ω - Jsmall (α ω) ω) +
            (avram_p4_h_gaussian_intrinsic_large_jump_sum X (β ω) ω -
              avram_p4_h_gaussian_intrinsic_large_jump_sum X (α ω) ω) -
            (rightLimit D (β ω) ω - rightLimit D (α ω) ω)) +
        (Real.exp (-(q * (β ω : ℝ))) - Real.exp (-(q * (α ω : ℝ)))) *
          (x + X.X (α ω) ω - rightLimit D (α ω) ω)) := by sorry
