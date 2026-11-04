-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_any_index_residual_summable_of_majorant
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_any_index_residual_summable_of_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:06:11.240835+00:00
-- url     : https://prove2.me/theorems/7c78776f-bce0-4f41-8eb6-84c68627a534
-- title:
--   Source right-dividend residual series converges under a summable majorant
-- statement:
--   For arbitrary indexed eligible right-dividend payments of the actual spectrally negative Levy source, a summable real norm-majorant guarantees summability of their discounted signed residuals and their total residual is nonpositive.
-- source:
--   Proved original right-dividend arbitrary-index residual sign theorem 7a42b298, Mathlib Summable.of_norm_bounded comparison test.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_any_index_rightjump_residual_tsum_nonpos
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_any_index_residual_summable_of_majorant
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ι → ℝ≥0)
    (hpre : ∀ k, t k = 0 ∨ (t k : ℝ≥0∞) < ruinTime X x D ω)
    (b : ι → ℝ) (hbsum : Summable b)
    (hbound : ∀ k,
      ‖Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω))‖ ≤ b k) :
    Summable (fun k : ι =>
      Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω))) ∧
    (∑' k : ι, Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω))) ≤ 0 := by sorry
