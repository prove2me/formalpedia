-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_real_time_cash_atom_le_secant
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_real_time_cash_atom_le_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:40:57.05793+00:00
-- url     : https://prove2.me/theorems/9f871587-ba43-41e3-ac2c-7fd1940e95c8
-- title:
--   Real-indexed genuine Cash singleton atom satisfies original HJB secant inequality
-- statement:
--   Transfers the original right-dividend Cash singleton inequality from NNReal clock time to a nonnegative real-valued atomic time t. This is the exact scalar-index bridge needed for the source P4-D atomic set A:Set ℝ, avoiding an unsupported identification of real and NNReal index sets.
-- source:
--   Proved original Cash atom-to-value-loss theorem P4-F c9b06745, Mathlib Real.coe_toNNReal, original P4-D measure index ℝ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_discounted_cash_atom_le_value_loss
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_real_time_cash_atom_le_secant
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
    (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (μatom : Measure ℝ)
    (hμatom : μatom {t} =
      ENNReal.ofReal (rightLimit D (Real.toNNReal t) ω -
        D (Real.toNNReal t) ω))
    (hdelta : 0 ≤ rightLimit D (Real.toNNReal t) ω -
      D (Real.toNNReal t) ω)
    (helig : Real.toNNReal t = 0 ∨
      (Real.toNNReal t : ℝ≥0∞) < ruinTime X x D ω) :
    (ENNReal.ofReal (Real.exp (-(q * t))) * μatom {t}).toReal ≤
      Real.exp (-(q * t)) *
        (w (riskProcess X x D (Real.toNNReal t) ω) -
          w (riskProcess X x D (Real.toNNReal t) ω -
            (rightLimit D (Real.toNNReal t) ω -
              D (Real.toNNReal t) ω))) := by sorry
