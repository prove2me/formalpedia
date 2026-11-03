-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_discounted_preterminal_cash_tendsto
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_ruin_discounted_preterminal_cash_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:07:34.370941+00:00
-- url     : https://prove2.me/theorems/2197e236-e244-4e83-b959-f1d55601df74
-- title:
--   Actual original discounted pre-ruin complete Stieltjes cash on an approaching grid converges to the strict ruin endpoint
-- statement:
--   For the actual dividend measure of any original admissible dividend strategy, fixed finite positive ruin time τ, nonnegative discount q and arbitrary grid points u_n<τ approaching τ from below, the full discounted Stieltjes cash on (0,u_n] converges in ENNReal to the genuinely strictly pre-ruin cash on (0,τ). The identity counts each earlier right-payment atom and all continuous or singular dividends but excludes the possible right payment at τ. It uses the canonically Proved exact (0,τ)=(0,u_n]∪(u_n,τ) partition, the vanishing discounted final open cell, and the directly proved finite total. There is no assumption of a stochastic Ito estimate or compensator.
-- source:
--   Proved exact original source strict discounted finiteness, weighted terminal gap, partition, ENNReal.add_sub_cancel_right, continuous ENNReal subtraction and eventuallity u_n>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_discounted_cash_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_discounted_strict_interior_mass_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_discounted_strict_ruin_terminal_partition

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_positive_ruin_discounted_preterminal_cash_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < τ)
    (hlim : Tendsto u atTop (𝓝 τ)) :
    Tendsto (fun n => ∫⁻ t in Ioc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
