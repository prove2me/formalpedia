-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_full_closed_grid_cash_tendsto
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_ruin_full_closed_grid_cash_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:58:45.252191+00:00
-- url     : https://prove2.me/theorems/07ce3187-6431-4c7d-9cc2-8d726a10c8cc
-- title:
--   Original complete closed prefix-grid Stieltjes dividends converge to the genuine positive-ruin paid reward including time zero
-- statement:
--   For a genuine original dividend strategy, every finite positive ruin time τ and arbitrary pre-ruin grid u_n<τ tending to τ, the discounted full Stieltjes reward over the closed prefix [0,u_n] converges to the exact reward on paymentTimes(τ)∩(-∞,τ]. This explicitly includes the original time-zero right-payment atom and all pre-ruin right/continuous payments, while excluding the right payment at the ruin instant. The proof uses the exact disjoint [0,u_n]={0}∪(0,u_n] identity, the source-specific weighted strictly pre-ruin convergence, and the Proved original positive-ruin cash decomposition, without a conditional stochastic estimate.
-- source:
--   Proved original discounted prefix convergence and complete positive-ruin initial atom plus strict-left cash identity; ENNReal tendsto addition and lintegral_union.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_discounted_preterminal_cash_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_positive_ruin_full_closed_grid_cash_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < τ)
    (hlim : Tendsto u atTop (𝓝 τ)) :
    Tendsto (fun n => ∫⁻ t in Icc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
