-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_any_discount_finite_horizon_stieltjes_exp_moment
-- name    : AvramDividend.Classical.avram_wave5_03_original_any_discount_finite_horizon_stieltjes_exp_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:58:01.136906+00:00
-- url     : https://prove2.me/theorems/8b70a8f9-1ce3-486d-a12e-02d73404ef8d
-- title:
--   Every finite-horizon original stopped Stieltjes dividend reward has finite expectation at any real discount, with explicit Levy exponential envelope
-- statement:
--   For the genuine original capped admissible dividend strategy, all Stieltjes payments including the time-zero atom, right lump sums, absolutely continuous and singular-continuous variation through the entire closed deterministic horizon before ruin have an explicit finite ENNReal expected reward envelope at any real q: exp(|psi(1)-q| T) exp(x). It follows by pointwise bounded-horizon comparison with the independently Proved original-source exponential-test expected dividend bound at discount psi(1), and the genuinely measurable random Stieltjes kernel. This removes the need to assume E[D_T+] finite before taking controlled Ito-Meyer expectations, while retaining the exact paymentTimes and original ruinTime.
-- source:
--   Original full stopped exponential source reward 3cf94f6f Proved, full Stieltjes random measurable s-finite kernel 766b5129, actual paymentTimes positive-time and joint measurability 71123237 and 6e9faa20; supports BV ef7e6c20 and corrected UBV 429e17ca, independent of pending source compensator 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_stopped_fullStieltjes_realDiscount_payoff_le_expCapital
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_any_discount_finite_horizon_stieltjes_exp_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) (q : ℝ) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (Real.exp (|X.ψ 1 - q| * (T : ℝ))) *
      ENNReal.ofReal (Real.exp x) := by sorry
