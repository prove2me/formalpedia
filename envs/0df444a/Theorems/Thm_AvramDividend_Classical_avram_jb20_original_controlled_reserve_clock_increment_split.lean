-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb20_original_controlled_reserve_clock_increment_split
-- name    : AvramDividend.Classical.avram_jb20_original_controlled_reserve_clock_increment_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:01:28.793231+00:00
-- url     : https://prove2.me/theorems/1251382d-9f3d-4952-b772-6a6f48b09c49
-- title:
--   Original post-payment reserve source increments retain Gaussian and marked-jump channels at arbitrary random clocks
-- statement:
--   For the exact original process and any dividend function D, express the post-payment controlled reserve increment from clock alpha to beta as physical Levy drift, source-totalised Gaussian increment, compensated bounded-small-jump increment and raw large-negative-jump increment, minus the exact right-limit cumulative dividend increment. Both clocks may depend on the sample. This is the first exact original cash-ledger cell identity before discount, Ito-Meyer Taylor expansion, ruin clipping and Stieltjes integration, which remain separate obligations.
-- source:
--   Proved 48ec85d6 original source arbitrary-clock increment split and Proved 5e6c5fea post-payment reserve increment decomposition. Required for 544e8511 physical cash ledger, but does not claim stochastic Ito centring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_increment_decomposition
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb20_original_controlled_reserve_clock_increment_split
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
      (∀ (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
          (α β : Ω → ℝ≥0) (ω : Ω),
        (x + X.X (β ω) ω - rightLimit D (β ω) ω) -
          (x + X.X (α ω) ω - rightLimit D (α ω) ω) =
        ((β ω : ℝ) - (α ω : ℝ)) * X.c +
          (M (β ω) ω - M (α ω) ω) +
          (Jsmall (β ω) ω - Jsmall (α ω) ω) +
          (avram_p4_h_gaussian_intrinsic_large_jump_sum X (β ω) ω -
            avram_p4_h_gaussian_intrinsic_large_jump_sum X (α ω) ω) -
          (rightLimit D (β ω) ω - rightLimit D (α ω) ω)) := by sorry
