-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:04:28.647359+00:00
-- url     : https://prove2.me/theorems/56246051-4c04-499f-b752-a890321b8762
-- title:
--   Original positive finite ruin complete discounted cash splits into time-zero payment and strictly pre-ruin dividends
-- statement:
--   At any positive finite true ruin time τ, the exact source paymentTimes convention includes the possible initial right dividend at time zero and all strictly positive payments before τ, but excludes any right dividend at τ. For the full genuine original Stieltjes measure and discounted weight, the stopped reward equals the sum of its time-zero singleton and strictly pre-ruin open interval rewards, including all diffuse and interior atomic mass. This handles the actual pre/post-payment convention without a stochastic estimate.
-- source:
--   Same-source paymentTimes strict positive ruin lemma, ENNReal.ofReal_lt_coe_iff, exact disjoint union and Mathlib lintegral_union.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (τ : ℝ≥0) (hτ : 0 < τ) :
    (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in ({(0 : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
