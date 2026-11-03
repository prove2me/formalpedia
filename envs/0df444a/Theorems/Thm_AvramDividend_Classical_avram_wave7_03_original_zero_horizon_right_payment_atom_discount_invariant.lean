-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_zero_horizon_right_payment_atom_discount_invariant
-- name    : AvramDividend.Classical.avram_wave7_03_original_zero_horizon_right_payment_atom_discount_invariant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:04:46.96987+00:00
-- url     : https://prove2.me/theorems/44fb28f1-9ff4-4315-8ebd-c3e81a5e19c3
-- title:
--   Full original time-zero right-limit dividend payment atom is discount-invariant even at immediate ruin
-- statement:
--   On the actual original Lévy process and ruin time, the genuine source ENNReal discounted Stieltjes payout over paymentTimes(ruinTime)∩Iic 0 is identical for arbitrary real discount rates q1 and q2. The result retains the original t=0 right-payment atom even if ruinTime=0, and follows from the already Proved exact original zero-horizon Stieltjes atom identity; no surrogate measure or process.
-- source:
--   Proved original full time-zero Stieltjes atom theorem avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_zero_horizon_right_payment_atom_discount_invariant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q₁ q₂ : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q₁ * t)))
        ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q₂ * t)))
        ∂(dividendMeasure D ω)) := by sorry
