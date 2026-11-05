-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_random_clock_cash_atom_hjb
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_random_clock_cash_atom_hjb
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:28:33.060237+00:00
-- url     : https://prove2.me/theorems/7367e5fe-71b7-4e25-b67f-b328235375b6
-- title:
--   Literal original random-clock Stieltjes Cash and physical paid-atom ENNReal HJB budget
-- statement:
--   For the exact source random clock and source full Cash hypothesis, extract a countable original paid nonzero right-dividend atom carrier with literal real Cash equal to discounted atom series plus diffuse Stieltjes integral. The discounted ENNReal atomic cash series is bounded by the original HJB right-jump value-loss series without integrability of the latter. Original time zero, surviving horizon inclusion and ruin exclusion follow automatically from the paymentTimes source support.
-- source:
--   Previously accepted aa561d4b physical Cash decomposition, c5fbf7f7 source paid-atom evidence, and 47c5a92b ENNReal value-loss summation; no pending helper imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_full_cash_paid_nonzero_atom_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_random_clock_cash_atom_hjb
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hjump : ∀ (ω : Ω) (u : ℝ≥0),
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D u ω - D u ω ≤
          w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      let E : Set ℝ := {t | t ∈ A ∧
        t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
      A.Countable ∧
      Cash ω =
        (∑' a : E,
          (ENNReal.ofReal (Real.exp (-(q * a.1))) *
            μatom {a.1}).toReal) +
        (∫⁻ s : ℝ,
          (if s ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * s))) else 0)
            ∂μdiffuse).toReal ∧
      (∑' a : E,
        ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}) ≤
      ∑' a : E,
        ENNReal.ofReal (Real.exp (-(q * a.1))) *
          ENNReal.ofReal
            (w (riskProcess X x D (Real.toNNReal a.1) ω) -
              w (riskProcess X x D (Real.toNNReal a.1) ω -
                (rightLimit D (Real.toNNReal a.1) ω -
                  D (Real.toNNReal a.1) ω))) := by sorry
