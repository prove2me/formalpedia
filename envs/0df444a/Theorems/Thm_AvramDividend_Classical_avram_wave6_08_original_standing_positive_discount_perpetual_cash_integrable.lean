-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_standing_positive_discount_perpetual_cash_integrable
-- name    : AvramDividend.Classical.avram_wave6_08_original_standing_positive_discount_perpetual_cash_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:41:01.2898+00:00
-- url     : https://prove2.me/theorems/2d1232f2-9bc3-4955-898b-06443d2d16bc
-- title:
--   Standing original Lévy complete perpetual dividend cash is L1 for every positive discount
-- statement:
--   For any Standing original spectrally negative Lévy X, admissible capped dividend D and any positive q, the complete strictly pre-ruin *untruncated* discounted Stieltjes cash.toReal is P-integrable. The true source positive Laplace root φ(q)>0 with ψφ=q gives the needed exponential tilt, so this is unconditional in positive q and does not require q≥ψ1, a bounded random clock, or any Ito–Meyer identity.
-- source:
--   Source standing positive ψ-root Proved UUID 1da68fa5 plus source perpetual θ-full-Stieltjes L1 Proved UUID 5b1a666c. Independent Chat08 integrable Cash export matching corrected 429e17ca source q>0/Standing premises; no stochastic estimate assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_stieltjes_cash_integrable_q_ge_psi
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_standing_positive_discount_perpetual_cash_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by sorry
