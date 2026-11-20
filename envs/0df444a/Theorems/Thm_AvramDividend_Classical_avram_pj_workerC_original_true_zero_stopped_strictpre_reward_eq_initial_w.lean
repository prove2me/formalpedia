-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_true_zero_stopped_strictpre_reward_eq_initial_w
-- name    : AvramDividend.Classical.avram_pj_workerC_original_true_zero_stopped_strictpre_reward_eq_initial_w
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:42:02.749201+00:00
-- url     : https://prove2.me/theorems/3a4e218b-dd2e-4bb2-97e4-7821f03f43c6
-- title:
--   Actual original zero stopped clock strict preterminal discounted reserve plus strict paymentTimes cash is exactly w(x)
-- statement:
--   For the genuine original spectrally negative Lévy path X and actual original admissible right-continuous dividends D, let the strict-preterminal reward V consist of discounted w evaluated at riskProcess X x D at stopping clock rho, plus the true original discounted dividendMeasure restricted to paymentTimes(ruinTime X x D)∩Iio(rho). At any sample with rho=0, V=w(x) exactly: X.X0=0, D0=0 and the strict negative-time dividend integrand has zero measure. This is the true zero-clock branch needed to split the unresolved positive stopped purejump Ito source, preserving the distinction from inclusive Iic cash for the final closed reward G.
-- source:
--   Proved 72bf4190 original strict Iio(0) cash vanishing; genuine X.X_zero and IsAdmissibleLe. Supports 51a5d40e fixedband and 8b446f5c existential physical Ito source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger125_original_zero_clock_cash_components_vanish
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_true_zero_stopped_strictpre_reward_eq_initial_w
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ρ : Ω → ℝ≥0)
    (V : Ω → ℝ)
    (hV : ∀ ω, V ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, ρ ω = 0 → V ω = w x := by sorry
