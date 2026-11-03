-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_uniform_unbounded_clocks_theta_budget
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_discount_uniform_unbounded_clocks_theta_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:01:49.927361+00:00
-- url     : https://prove2.me/theorems/ac3d2116-9006-4cff-9615-24a897bc8039
-- title:
--   One strictly positive source Esscher tilt controls all original unbounded random-clock dividend rewards for every q>0
-- statement:
--   For every original spectrally negative Lévy X and q>0 there exists one θ>0, chosen independently of random clocks, such that the actual full-Stieltjes ruin-stopped discounted expected dividend cash on every measurable possibly unbounded random clock is bounded after θ scaling by exp(θx). No Standing and no mixed-source Ito law.
-- source:
--   Source positive small tilt 6b7f5580 and original θ random-clock expectation 223bc8fc. Uniform quantitative stopped source cash envelope at every q>0, needed for bounded-localizer to unbounded-horizon limit, strictly independent from hSourceLimit or any Ito assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_positive_discount_uniform_unbounded_clocks_theta_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧
      ∀ (τ : Ω → ℝ≥0)
        (hτmeas : Measurable (fun ω => (τ ω : ℝ))),
      ENNReal.ofReal θ *
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) ≤
        ENNReal.ofReal (Real.exp (θ * x)) := by sorry
