-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_unbounded_clock_cash_integrable_no_standing
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_discount_unbounded_clock_cash_integrable_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:46:57.298195+00:00
-- url     : https://prove2.me/theorems/594e2b54-ca43-456d-97ad-d0c084997508
-- title:
--   Original Lévy positive-discount unbounded-clock dividend cash L1 without Standing
-- statement:
--   Any original spectrally negative Lévy process, not necessarily Standing, supports P-integrable real ruin-stopped full-Stieltjes discounted cash at every positive q and arbitrary measurable finite-valued random clock; choose a sufficiently small positive Esscher parameter from ψ(0)=0 and continuity.
-- source:
--   Original ψ-zero theorem 88416f41; source ψ half-line continuity 1fa27b74; original arbitrary-clock θ cash L1 006d9506. Independent fundamental source cash bound with no Standing, for corrected UBV verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_positive_discount_unbounded_clock_cash_integrable_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by sorry
