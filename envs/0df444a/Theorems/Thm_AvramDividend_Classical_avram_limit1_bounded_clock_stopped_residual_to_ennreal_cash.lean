-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_bounded_clock_stopped_residual_to_ennreal_cash
-- name    : AvramDividend.Classical.avram_limit1_bounded_clock_stopped_residual_to_ennreal_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:38:56.134187+00:00
-- url     : https://prove2.me/theorems/b443283f-afc6-4974-aefd-95b13427a845
-- title:
--   Original bounded stopped Itô residual with nonnegative terminal and centred martingale controls genuine dividend cash
-- statement:
--   Given an actual capped-admissible original spectrally negative Lévy dividend strategy, bounded measurable random clock τ, and the source-exact real stopped Cash equal to the original fibre ENNReal integral converted to Real, assume Cash and the martingale M are integrable, mean(M)=0, the stopped terminal Term is nonnegative almost everywhere, the drift residual G+H is nonpositive almost everywhere, and the genuine pathwise a.e. stopped residual Term+Cash ≤ B+M+G+H. Then the actual double ENNReal discounted dividend integral on paymentTimes(ruinTime) ∩ Iic τ is ≤ ENNReal.ofReal B. Integrate the pointwise Cash ≤ B+M inequality via the pinned Mathlib integral_mono_ae and P probability, then the Proved bounded-random-clock toReal→ENNReal bridge d9993239. Term itself need not be integrable; its nonnegativity suffices. The theorem does not assert the stochastic residual, martingale centring, or terminal sign.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_bounded_clock_stopped_residual_to_ennreal_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ) (Cash Term M G H : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hMI : Integrable M P)
    (hMZero : (∫ ω, M ω ∂P) = 0)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hGHNonpos : ∀ᵐ ω ∂P, G ω + H ω ≤ 0)
    (hResidual : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ B + M ω + G ω + H ω) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
