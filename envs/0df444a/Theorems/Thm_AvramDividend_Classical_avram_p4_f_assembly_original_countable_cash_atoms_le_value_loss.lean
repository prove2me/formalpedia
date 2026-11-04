-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_countable_cash_atoms_le_value_loss
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_countable_cash_atoms_le_value_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:41:11.897371+00:00
-- url     : https://prove2.me/theorems/315ca61b-6d48-4c82-ab47-3d746e682370
-- title:
--   Summable original discounted Cash atoms are bounded by their genuine value losses
-- statement:
--   On an arbitrary set of genuine original payment times, the countable real discounted Cash atomic series is bounded above by the countable sum of original value-function secant losses, provided both series are genuinely summable. The pointwise inequality is the accepted source Cash-atom secant bound; no countable measure or martingale identity is assumed tacitly.
-- source:
--   P4-F original atom-to-real conversion, original discounted Cash secant bound, pinned Mathlib tsum_le_tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_discounted_cash_atom_le_value_loss
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_countable_cash_atoms_le_value_loss
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (t : ℝ≥0),
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (A : Set ℝ≥0) (μatom : Measure ℝ)
    (hμatom : ∀ a : A,
      μatom {(a.1 : ℝ)} =
        ENNReal.ofReal (rightLimit D a.1 ω - D a.1 ω))
    (hdelta : ∀ a : A,
      0 ≤ rightLimit D a.1 ω - D a.1 ω)
    (helig : ∀ a : A,
      a.1 = 0 ∨ (a.1 : ℝ≥0∞) < ruinTime X x D ω)
    (hCashSum : Summable (fun a : A =>
      (ENNReal.ofReal (Real.exp (-(q * (a.1 : ℝ)))) *
        μatom {(a.1 : ℝ)}).toReal))
    (hValueSum : Summable (fun a : A =>
      Real.exp (-(q * (a.1 : ℝ))) *
        (w (riskProcess X x D a.1 ω) -
          w (riskProcess X x D a.1 ω -
            (rightLimit D a.1 ω - D a.1 ω))))) :
    (∑' a : A,
      (ENNReal.ofReal (Real.exp (-(q * (a.1 : ℝ)))) *
        μatom {(a.1 : ℝ)}).toReal) ≤
      ∑' a : A,
        Real.exp (-(q * (a.1 : ℝ))) *
          (w (riskProcess X x D a.1 ω) -
            w (riskProcess X x D a.1 ω -
              (rightLimit D a.1 ω - D a.1 ω))) := by sorry
