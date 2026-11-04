-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_cash_countable_rightatom_sum_and_diffuse
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_real_cash_countable_rightatom_sum_and_diffuse
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:48:09.049453+00:00
-- url     : https://prove2.me/theorems/f897c004-e02d-44d0-9675-58631eae319f
-- title:
--   Original real stopped Cash equals finite countable right-payment atom sum plus diffuse part with exact rightLimit masses
-- statement:
--   The actual original ruin-stopped Cash at a finite closed [0,T] horizon is exactly the sum of a countable source right-atomic payment series and an atomless (including singular-continuous) Stieltjes contribution. Every atomic singleton is the actual rightLimit D t-D t payment, including t=0 and t=T. For nonnegative discount q, source Cash is bounded by the finite rightLimit D T, so both components are finite ENNReal quantities and the exact identity survives toReal conversion, suitable for P4-F's integrable signed residual.
-- source:
--   Source-proved countable original atomic Cash decomposition e247750f (pending proof admission); source-proved finite discounted Cash bound 1a006d5f; pinned NullSingletonClass, Measure add singleton, ENNReal.toReal_add; Avram Prop. 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightatomic_discounted_cash_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Source-original real Cash is an exact countable right-atom sum and diffuse component. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_real_cash_countable_rightatom_sum_and_diffuse
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
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) ∧
      (∀ t : ℝ≥0, t ≤ T →
        μatom {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      ((∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
          (∑' a : A, f a.1 * μatom {a.1}).toReal +
          (∫⁻ s : ℝ, f s ∂μdiffuse).toReal) := by sorry
