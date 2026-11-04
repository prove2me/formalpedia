-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_implies_ae_random_strict_future_signed_integrable
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_value_implies_ae_random_strict_future_signed_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:07:15.927792+00:00
-- url     : https://prove2.me/theorems/1c1d4225-0b89-4c98-ac32-f1e52c315981
-- title:
--   Finite original expected dividends imply real Stieltjes integrability over every random strict-future window
-- statement:
--   For the actual original spectrally negative Lévy process under P and dividendMeasure D ω, finite canonical dividendValue implies almost-sure signed real discounted Stieltjes integrability on paymentTimes(ruinTime) ∩ Ioi(T ω) for any sample-dependent real clock T, with no clock measurability assumption. The restriction retains all continuous and right-jump cash after T and excludes the clock atom. It supplies the exact integrability premise of the signed strict-future envelope-to-ENNReal bridge.
-- source:
--   Already Proved theorem 3a9d20cb-d6ee-405d-957d-cdcd382919cd supplies full original unrestricted IntegrableOn. Pinned Mathlib MeasureTheory.IntegrableOn.mono restricts it to paymentTimes ∩ Ioi(T ω) on the same original dividendMeasure D ω.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_value_implies_ae_random_strict_future_signed_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (T : Ω → ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω))
        (dividendMeasure D ω) := by sorry
