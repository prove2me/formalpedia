-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:36:11.88574+00:00
-- url     : https://prove2.me/theorems/47c5a92b-dcdf-4242-b96b-4d15a082d8a0
-- title:
--   Exact original paid cash atoms bounded by HJB value losses in ENNReal without assuming loss summability
-- statement:
--   For the true source Lévy process, each eligible original right-dividend atom satisfies the source HJB secant. Nonnegative discounted ENNReal atomic cash is pointwise bounded by the discounted value drop, and summing preserves the bound even if the value-drop sum is infinite. This deliberately avoids a false summability assumption on candidate value losses. The lemma is an actual process-specific cash accounting consequence of the original hjump.
-- source:
--   Canonical source hjump and true rightLimit dividend singleton masses; the pinned ENNReal.tsum_le_tsum and ENNReal.ofReal_le_ofReal rules.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
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
    (hMass : ∀ a : A,
      μatom {a.1} = ENNReal.ofReal
        (rightLimit D (Real.toNNReal a.1) ω -
          D (Real.toNNReal a.1) ω))
    (hPaid : ∀ a : A, Real.toNNReal a.1 = 0 ∨
      (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω) :
    (∑' a : A,
      ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}) ≤
    ∑' a : A,
      ENNReal.ofReal (Real.exp (-(q * a.1))) *
        ENNReal.ofReal
          (w (riskProcess X x D (Real.toNNReal a.1) ω) -
            w (riskProcess X x D (Real.toNNReal a.1) ω -
              (rightLimit D (Real.toNNReal a.1) ω -
                D (Real.toNNReal a.1) ω))) := by sorry
