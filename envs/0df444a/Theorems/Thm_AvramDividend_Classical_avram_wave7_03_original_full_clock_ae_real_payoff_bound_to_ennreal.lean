-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_clock_ae_real_payoff_bound_to_ennreal
-- name    : AvramDividend.Classical.avram_wave7_03_original_full_clock_ae_real_payoff_bound_to_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:47:48.483369+00:00
-- url     : https://prove2.me/theorems/91cb446b-409a-45be-8937-9ce1e76b3465
-- title:
--   Original finite-clock pathwise real Stieltjes payoff domination transfers under the ENNReal expectation
-- statement:
--   On the original spectrally negative Lévy sample space P, with the actual cumulative dividend strategy D, ruin time and complete Stieltjes dividend measure, any almost-sure real domination of the full finite-clock cash.toReal by a path-dependent real G transfers to an extended nonnegative expectation inequality with ENNReal.ofReal G. This uses the Proved a.e. finiteness of true original stopped full Stieltjes cash; no integrability, measurability or finiteness of G is assumed, so the RHS may be infinite. Initial payment at zero, all strictly pre-ruin interior atoms and diffuse cash are retained without altering the domain.
-- source:
--   Canonical original dividend definition 561c1e83; Proved original stopped cash pathwise a.e. finite f0d4c94c-c070-460b-bb90-95ccc0264d90; ENNReal.ofReal_toReal; lintegral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_full_clock_ae_real_payoff_bound_to_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ)
    (G : Ω → ℝ)
    (hPath : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ≤ G ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) := by sorry
