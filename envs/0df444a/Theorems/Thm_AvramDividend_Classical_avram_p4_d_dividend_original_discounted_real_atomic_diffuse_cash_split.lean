-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_discounted_real_atomic_diffuse_cash_split
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_discounted_real_atomic_diffuse_cash_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:36:52.416598+00:00
-- url     : https://prove2.me/theorems/e8d77adc-767b-4d13-ad15-e6a382fdb338
-- title:
--   Exact original discounted Stieltjes atomic/diffuse Cash splitting after real conversion at finite horizon
-- statement:
--   For the original Levy source, admissible dividend strategy and a finite closed [0,T] payment window with q≥0, combine the proved actual atomic/diffuse Cash equality with the source-discounted Stieltjes cash bound by rightLimit D T. This ensures both components are finite ENNReal values. Their exact equality survives conversion to real Cash, retaining the time-zero atom, surviving horizon payment atom and all singular continuous mass, and is ready for real-valued Itô–Meyer signed remainder integration.
-- source:
--   Proved P4-D original exact discounted atomic/diffuse Cash decomposition 2fe782b8; proved source discounted rightLimit bound 1a006d5f; pinned Mathlib ENNReal.toReal_add, ofReal_lt_top; Avram Proposition 4(i), Eq. 5.13.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_discounted_closed_atomic_diffuse_cash_split
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original closed discounted atom/diffuse Cash split remains exact in real L¹ units. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_discounted_real_atomic_diffuse_cash_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    let f : ℝ → ℝ≥0∞ := fun s =>
      if s ∈ paymentTimes (ruinTime X x D ω)
      then ENNReal.ofReal (Real.exp (-(q * s))) else 0
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      NullSingletonClass μdiffuse ∧
      μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) ∧
      ((∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
          (∫⁻ s : ℝ, f s ∂μatom).toReal +
          (∫⁻ s : ℝ, f s ∂μdiffuse).toReal) := by sorry
