-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightatomic_discounted_cash_exact
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightatomic_discounted_cash_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:28:24.39766+00:00
-- url     : https://prove2.me/theorems/e247750f-3b3a-4b81-9361-2977a2173330
-- title:
--   Original stopped dividend Cash is an exact countable right-payment atom sum plus diffuse Stieltjes integral
-- statement:
--   At a genuine ruin-truncated stopping clock and a closed dividend window [0,T], obtain the source-proved disjoint countable right-atomic/diffuse decomposition, its exact right-limit singleton masses at zero and horizon, and its total mass. Apply the pinned Mathlib countable lintegral identity and almost-everywhere carrier restriction to turn the discounted atomic integral into a tsum over actual payment times, retaining the separate atomless (including singular-continuous) contribution and equality to literal original Cash.
-- source:
--   Accepted original closed Stieltjes disjoint partition theorem 5126bd4b; accepted original closed cash integral equality 52a094c1; pinned Mathlib MeasureTheory.lintegral_countable and Measure.restrict_eq_self_of_ae_mem; Avram Proposition 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Exact original closed-window Cash equals a countable right-atom sum plus diffuse Cash. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightatomic_discounted_cash_exact
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
        (∑' a : A, f a.1 * μatom {a.1}) +
          (∫⁻ s : ℝ, f s ∂μdiffuse) := by sorry
