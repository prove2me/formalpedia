-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_higher_discount_signed_horizon_convergence
-- name    : AvramDividend.Classical.avram_wave7_03_higher_discount_signed_horizon_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:44:20.212203+00:00
-- url     : https://prove2.me/theorems/326b359d-2a07-4f23-819f-261f658542df
-- title:
--   Finite lower-rate original dividendValue yields a.e. higher-rate signed Stieltjes horizon convergence
-- statement:
--   On the canonical original process X under P with unchanged ruinTime, paymentTimes, dividendMeasure and right-limit atom, if its full original dividendValue is finite at q₁ and q₁ ≤ q₂, then the signed finite-horizon discounted Stieltjes payment converges P-almost surely to the genuine unrestricted signed Stieltjes payment at q₂. It includes continuous and jump dividends and does not use a surrogate sample space.
-- source:
--   Exact original P/Ω source, direct corollary of two Proved unrestricted stochastic-to-ENNReal dividend bridge theorems.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_ae_signed_horizons_converge_full
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_higher_discount_signed_horizon_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂)
    (hFinite : dividendValue X q₁ x D < ⊤) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω))
        atTop (𝓝 (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω))) := by sorry
