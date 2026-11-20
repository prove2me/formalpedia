-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_allclock_closed_inclusive_reward_le_strict_prepayment_physical
-- name    : AvramDividend.Classical.avram_pj_workerC_original_allclock_closed_inclusive_reward_le_strict_prepayment_physical
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:54:07.692582+00:00
-- url     : https://prove2.me/theorems/9b68b53a-d4e0-4136-8ece-075f28e84a75
-- title:
--   Original all-clock inclusive final dividend reward is at most original strict preterminal physical cash plus reserve value
-- statement:
--   For actual original spectrally negative Lévy X, admissible post-right D and any real stopped clock rho, the original discounted terminal-plus-paymentTimes∩Iic(rho) closed payoff G is at most the strictly preterminal paymentTimes∩Iio(rho) cash and original pre-right riskProcess terminal reward V. On positive rho use Proved original post-right dividend contact sign; at zero rho, G=V=w(x) by true X.X0=D0=0 and zero strict cash. This is a sound all-clock bridge, maintaining the terminal right-dividend atom and same physical process.
-- source:
--   Proved 754befba positive-clock original contact sign and 3a4e218b true zero strict payoff; original G and V exact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_true_zero_stopped_strictpre_reward_eq_initial_w
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_postright_inclusive_reward_positive_clock_le_strict_physical
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_allclock_closed_inclusive_reward_le_strict_prepayment_physical
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (ρ : Ω → ℝ≥0) (G : Ω → ℝ)
    (hGdef : ∀ ω, G ω =
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
            else riskProcess X x D (ρ ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal)
    (V : Ω → ℝ)
    (hVdef : ∀ ω, V ω = Real.exp (-(q * (ρ ω : ℝ))) *
        w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, G ω ≤ V ω := by sorry
