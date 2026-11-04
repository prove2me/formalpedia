-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_discounted_rightjump_residual_nonpos
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_discounted_rightjump_residual_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:23:50.250215+00:00
-- url     : https://prove2.me/theorems/2c74f926-f401-4df2-a431-0f75ca41d7f3
-- title:
--   True original-process discounted right-payment secant residual is nonpositive
-- statement:
--   At every actual admissible payment time, the original process's local jump budget implies nonpositivity of the discounted dividend-versus-value-loss residual. This holds for any real discount q, using strict positivity of the exponential factor, and preserves the actual original reserve and right-limit cash jumps.
-- source:
--   Original P4-F stopped Itô residual 0dda1be7, genuine jump admissibility side condition, original rightLimit and riskProcess definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_discounted_rightjump_residual_nonpos
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
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) -
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))) ≤ 0 := by sorry
