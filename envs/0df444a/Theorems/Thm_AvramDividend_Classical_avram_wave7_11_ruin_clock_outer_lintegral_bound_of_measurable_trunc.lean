-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ruin_clock_outer_lintegral_bound_of_measurable_trunc
-- name    : AvramDividend.Classical.avram_wave7_11_ruin_clock_outer_lintegral_bound_of_measurable_trunc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:34:21.74075+00:00
-- url     : https://prove2.me/theorems/c74c5b53-8659-429a-bb6b-128f8173c9b5
-- title:
--   Uniform truncated-ruin Stieltjes expectations bound the full-ruin expectation under explicit measurability
-- statement:
--   For the same original dividend-measure kernel ω↦dividendMeasure D ω and random ruin horizon σ(ω), uniform expected discounted Stieltjes payout bounds at every natural-number truncated ruin clock imply the full finite-T ruin-clock expected payout bound. The measurability of each truncated pathwise payout is stated explicitly, never inferred without proof from IsAdmissibleLe. The pathwise monotone limit is the separate source-faithful theorem cb688725; the outer ENNReal monotone convergence follows from measurable and increasing integrands. All original payment sets and t=0 atoms are preserved.
-- source:
--   Exact original stochastic finite-horizon expectation conclusion of canonical cc518136 and positive-capital uniform ruin budget 3c9532b7. Import verified inner-clock limit (new cb688725), Proved paymentTimes_min_mono_horizon 021cfe05 and pinned MeasureTheory.lintegral_iSup (remote signature with measurability and monotonicity). Additional hMeas is an explicit outstanding source-measurability lemma, not a hidden weakening of canonical assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_ruin_clock_outer_lintegral_bound_of_measurable_trunc
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q T : ℝ) (B : ℝ≥0∞)
    (hMeas : ∀ n : ℕ, Measurable (fun ω =>
      ∫⁻ t in paymentTimes (min (σ ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (σ ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B := by sorry
