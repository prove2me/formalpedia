-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_real_indexed_cash_atom_tsum_le_value_loss
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_real_indexed_cash_atom_tsum_le_value_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:51:12.873271+00:00
-- url     : https://prove2.me/theorems/c6787043-79de-4a60-91ce-d007f55d67f0
-- title:
--   Countable real-indexed source Cash atoms satisfy the original HJB value-loss sum budget
-- statement:
--   For the exact real-indexed atomic set A returned by the original P4-D source decomposition, if the selected atom times are nonnegative, carry actual right-payment singleton masses and both real series are summable, the countable Cash atom total is bounded by the genuine original HJB secant loss total. This avoids reindexing the entire set as NNReal.
-- source:
--   Original P4-F real-clock Cash-atom secant bridge and Mathlib Summable.tsum_le_tsum; retains genuine original riskProcess and rightLimit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_real_time_cash_atom_le_secant
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_real_indexed_cash_atom_tsum_le_value_loss
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
    (ω : Ω) (A : Set ℝ) (μatom : Measure ℝ)
    (hA0 : ∀ a : A, 0 ≤ a.1)
    (hμatom : ∀ a : A,
      μatom {a.1} = ENNReal.ofReal
        (rightLimit D (Real.toNNReal a.1) ω -
          D (Real.toNNReal a.1) ω))
    (hdelta : ∀ a : A,
      0 ≤ rightLimit D (Real.toNNReal a.1) ω -
        D (Real.toNNReal a.1) ω)
    (helig : ∀ a : A, Real.toNNReal a.1 = 0 ∨
      (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω)
    (hCashSum : Summable (fun a : A =>
      (ENNReal.ofReal (Real.exp (-(q * a.1))) *
        μatom {a.1}).toReal))
    (hValueSum : Summable (fun a : A =>
      Real.exp (-(q * a.1)) *
        (w (riskProcess X x D (Real.toNNReal a.1) ω) -
          w (riskProcess X x D (Real.toNNReal a.1) ω -
            (rightLimit D (Real.toNNReal a.1) ω -
              D (Real.toNNReal a.1) ω))))) :
    (∑' a : A,
      (ENNReal.ofReal (Real.exp (-(q * a.1))) *
        μatom {a.1}).toReal) ≤
      ∑' a : A, Real.exp (-(q * a.1)) *
        (w (riskProcess X x D (Real.toNNReal a.1) ω) -
          w (riskProcess X x D (Real.toNNReal a.1) ω -
            (rightLimit D (Real.toNNReal a.1) ω -
              D (Real.toNNReal a.1) ω))) := by sorry
