-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_source_stopped_reward_nonnegative
-- name    : AvramDividend.Classical.avram_ubv_top9_original_source_stopped_reward_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:49:59.65721+00:00
-- url     : https://prove2.me/theorems/16fd752a-2b2f-4e4d-8e3a-14deb460a4cb
-- title:
--   Original closed-clock stopped reward is pointwise nonnegative
-- statement:
--   For an arbitrary original spectrally negative Levy process, all original right-payment reserve and ruin/cemetery conventions and the exact closed-clock Iic discounted dividend measure, the stopped reward is nonnegative whenever the candidate value is globally nonnegative. The latter follows from the infinite-cap original HJB conditions.
-- source:
--   Exact original Fsource term from canonical theorem 148b2516. The nonnegative candidate interface is discharged by the separate source-exact global topcap theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_source_stopped_reward_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ∀ y : ℝ, 0 ≤ w y)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ k ω, 0 ≤ F k ω := by sorry
