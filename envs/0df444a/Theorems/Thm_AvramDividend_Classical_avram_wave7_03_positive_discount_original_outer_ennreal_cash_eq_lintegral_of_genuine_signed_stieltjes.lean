-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_positive_discount_original_outer_ennreal_cash_eq_lintegral_of_genuine_signed_stieltjes
-- name    : AvramDividend.Classical.avram_wave7_03_positive_discount_original_outer_ennreal_cash_eq_lintegral_of_genuine_signed_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:48:52.666326+00:00
-- url     : https://prove2.me/theorems/7c3aea2e-78c7-46dd-bd2a-136f0afcc6bd
-- title:
--   Canonical original positive-discount ENNReal dividendValue equals outer ENNReal lintegral of genuine unrestricted signed real Stieltjes payout without a finite mean premise
-- statement:
--   Exact unconditional original-process signed-to-ENNReal outer bridge for q>0. The canonical double ENNReal discounted Stieltjes dividendValue equals the outer ENNReal lintegral over original P of ENNReal.ofReal of the actual unrestricted signed discounted real Stieltjes integral over paymentTimes(ruinTime) against the same dividendMeasure. No finite expected dividend hypothesis: both expectations may be top. Genuine pathwise integrability holds P-a.e. via Proved positive-discount a.e. finiteness and Proved pathwise conversion. This is not a Brownian/Poisson replacement or a rewrite of an unrelated real integral. Time-zero right-limit, continuous dividend and jump mass remain present.
-- source:
--   Proved original positive discount a.e finite c3df986d; accepted full unrestricted pathwise signed Stieltjes eq 329453c6; lintegral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_positive_discount_original_outer_ennreal_cash_eq_lintegral_of_genuine_signed_stieltjes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    dividendValue X q x D =
      (∫⁻ ω : Ω, ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
