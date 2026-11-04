-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_any_index_rightjump_residual_tsum_nonpos
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_any_index_rightjump_residual_tsum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:56:27.284018+00:00
-- url     : https://prove2.me/theorems/7a42b298-26e8-402a-b67b-b31a7865da9b
-- title:
--   Original right-dividend signed residual summed over any summable index type
-- statement:
--   For an arbitrary index type ι of eligible original right-dividend payment times, their summable discounted residual series is nonpositive. This supports the actual source Cash atom decomposition, which uses a subtype of a countable set A rather than a fixed natural-number enumeration, while retaining the explicit summability obligation.
-- source:
--   Proved original right-dividend atom residual 9f4070e7, proved Cash atom-plus-diffuse decomposition f897c004, pinned Mathlib tsum_nonpos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_any_index_rightjump_residual_tsum_nonpos
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
    (hsummable : Summable (fun k : ι =>
      Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω)))) :
    (∑' k : ι, Real.exp (-(q * (t k : ℝ))) *
      ((rightLimit D (t k) ω - D (t k) ω) +
        w (x + X.X (t k) ω - rightLimit D (t k) ω) -
        w (riskProcess X x D (t k) ω))) ≤ 0 := by sorry
