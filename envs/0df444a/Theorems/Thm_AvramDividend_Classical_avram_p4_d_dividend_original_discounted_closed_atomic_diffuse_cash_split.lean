-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_discounted_closed_atomic_diffuse_cash_split
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_discounted_closed_atomic_diffuse_cash_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:16:41.000505+00:00
-- url     : https://prove2.me/theorems/2fe782b8-7e36-4f4a-ba58-19033a7d60e8
-- title:
--   Exact original discounted stopped dividend Cash splits into disjoint atomic and diffuse Stieltjes integrals
-- statement:
--   For the original spectrally negative Levy source and admissible dividend Stieltjes measure restricted to the full closed [0,T] window, obtain a countable right-atomic carrier and atomless diffuse measure with disjoint support, correct time-zero and horizon right atoms, and exact total mass. Apply the pinned Mathlib lintegral_add_measure identity and the accepted stopped Cash equality to split the literal ruin-truncated discounted Cash into its atomic and diffuse integrals without losing singular continuous payments or counting atoms twice.
-- source:
--   Accepted original closed right-atomic/diffuse disjoint partition 5126bd4b; accepted exact original closed stopped Cash identity 52a094c1; pinned Mathlib MeasureTheory.lintegral_add_measure type; Avram Proposition 4(i), Eq. 5.13.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original stopped dividend Cash splits exactly into disjoint right-atomic and diffuse discounted Stieltjes contributions. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_discounted_closed_atomic_diffuse_cash_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (ω : Ω) (T : ℝ≥0) :
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
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
        (∫⁻ s : ℝ, f s ∂μatom) + (∫⁻ s : ℝ, f s ∂μdiffuse) := by sorry
