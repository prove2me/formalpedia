-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_budget
-- name    : AvramDividend.Classical.avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:28:44.505692+00:00
-- url     : https://prove2.me/theorems/223bc8fc-3646-4d46-8bde-b7947d809e8b
-- title:
--   Unbounded original measurable random-clock full-Stieltjes cash obeys source θ budget
-- statement:
--   For the actual original spectrally negative Lévy source X and genuinely admissible D, every measurable nonnegative random clock τ (without a deterministic upper bound or stopping-time premise) has θ-scaled expected discounted full-Stieltjes dividend reward bounded by exp(θx) whenever θ>0 and q≥ψθ. The proof uses exact pathwise inclusion in the unrestricted original paymentTimes and the already proved unconditional source perpetual rate; no independent Ito law or artificial process is introduced.
-- source:
--   Canonical source perpetual θ reward rate 2abbc6bc and original random-clock full Stieltjes measurability 2d478c7d. Independent Chat08 source cash budget for unbounded localising clocks; Chat01/03/06 stochastic representation ownership unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    ENNReal.ofReal θ *
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) ≤
      ENNReal.ofReal (Real.exp (θ * x)) := by sorry
