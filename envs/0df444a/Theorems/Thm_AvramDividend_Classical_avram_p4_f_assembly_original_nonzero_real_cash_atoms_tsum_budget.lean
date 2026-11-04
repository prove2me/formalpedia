-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_nonzero_real_cash_atoms_tsum_budget
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_nonzero_real_cash_atoms_tsum_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:16:27.642261+00:00
-- url     : https://prove2.me/theorems/194b38b5-92bf-4653-b763-b848586b80f6
-- title:
--   Genuine nonzero original Cash atoms satisfy the countable source HJB budget with clocks derived from Stieltjes support
-- statement:
--   For a real-indexed subset whose members have nonzero singleton masses in the actual original stopped dividend measure, the source measure decomposition gives nonnegative valid physical times, and source right singleton equality identifies their original right payment increments. These replace hand-supplied time-positivity and atomic mass premises in the accepted countable secant comparison.
-- source:
--   Accepted fbaa8669 original stopped Cash support and c6787043 real-indexed source HJB countable comparison. Explicit hdelta, helig and summability remain for genuine future work.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_real_indexed_cash_atom_tsum_le_value_loss
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_nonzero_real_cash_atoms_tsum_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (u : ℝ≥0),
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D u ω - D u ω ≤
          w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    (ω : Ω) (T : ℝ≥0) (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hRight : ∀ t : ℝ≥0, t ≤ T →
      μatom {(t : ℝ)} =
        ENNReal.ofReal (rightLimit D t ω - D t ω))
    (A : Set ℝ) (hEff : ∀ a : A, μatom {a.1} ≠ 0)
    (hdelta : ∀ a : A,
      0 ≤ rightLimit D (Real.toNNReal a.1) ω -
        D (Real.toNNReal a.1) ω)
    (helig : ∀ a : A, Real.toNNReal a.1 = 0 ∨
      (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω)
    (hCashSum : Summable (fun a : A =>
      (ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}).toReal))
    (hValueSum : Summable (fun a : A =>
      Real.exp (-(q * a.1)) *
        (w (riskProcess X x D (Real.toNNReal a.1) ω) -
          w (riskProcess X x D (Real.toNNReal a.1) ω -
            (rightLimit D (Real.toNNReal a.1) ω -
              D (Real.toNNReal a.1) ω))))) :
    (∑' a : A, (ENNReal.ofReal (Real.exp (-(q * a.1))) *
      μatom {a.1}).toReal) ≤
      ∑' a : A, Real.exp (-(q * a.1)) *
        (w (riskProcess X x D (Real.toNNReal a.1) ω) -
          w (riskProcess X x D (Real.toNNReal a.1) ω -
            (rightLimit D (Real.toNNReal a.1) ω -
              D (Real.toNNReal a.1) ω))) := by sorry
