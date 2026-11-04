-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_full_real_decomposition_with_rightjump
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_full_real_decomposition_with_rightjump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:34:35.492194+00:00
-- url     : https://prove2.me/theorems/188366d0-922c-4104-b8ae-d82924b02fde
-- title:
--   True stopped Cash decomposes into summable real right atoms and diffuse Cash, retaining exact source jump masses
-- statement:
--   Strengthens original source real Cash atom-plus-diffuse identity by retaining the exact source singleton right-limit jump formula for every t≤T. The countable real atom series is summable, the diffuse cash remains exact, and the right-jump masses can directly feed the original HJB value-loss inequality.
-- source:
--   Proved P4-D full original Cash decomposition f897c004, with the source hRight side condition retained, and Proved P4-F atomic real-series lemma 152570c5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_cash_countable_rightatom_sum_and_diffuse
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atomic_series
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_full_real_decomposition_with_rightjump
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
      (∀ t : ℝ≥0, t ≤ T →
        μatom {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
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
