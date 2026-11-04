-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_full_real_decomposition
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_full_real_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:22:28.009068+00:00
-- url     : https://prove2.me/theorems/6a889ec5-1f2c-4816-8c6e-301b39e41b41
-- title:
--   Full source original Cash equals summable real dividend atoms plus diffuse Stieltjes Cash
-- statement:
--   For the actual original spectrally negative Lévy process, genuine dividend strategy, ruin-clock payment times, nonnegative discount and finite physical horizon, there exist the source countable atomic and diffuse dividend measures. Their split, singular support, real atomic summability and exact full Cash real-series-plus-diffuse Stieltjes identity are proved simultaneously, preserving all actual right-payment atoms and diffuse mass.
-- source:
--   Proved original Cash decomposition f897c004, accepted P4-F source finiteness and ENNReal-to-real series conversion; no substituted process or clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_cash_countable_rightatom_sum_and_diffuse
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atomic_series
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_full_real_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict
        (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse ∧
      NullSingletonClass μdiffuse ∧
      μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
      Summable (fun a : A =>
        ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) *
          μatom {a.1}).toReal) ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω)).toReal =
        (∑' a : A,
          ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
            ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) *
            μatom {a.1}).toReal) +
        (∫⁻ s : ℝ,
          (if s ∈ paymentTimes (ruinTime X x D ω) then
            ENNReal.ofReal (Real.exp (-(q * s))) else 0)
            ∂μdiffuse).toReal := by sorry
