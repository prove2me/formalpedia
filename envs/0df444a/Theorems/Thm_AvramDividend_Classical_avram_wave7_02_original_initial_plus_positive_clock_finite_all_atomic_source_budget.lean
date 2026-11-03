-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_plus_positive_clock_finite_all_atomic_source_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_initial_plus_positive_clock_finite_all_atomic_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:02:33.554389+00:00
-- url     : https://prove2.me/theorems/d1ae71c7-4fde-4682-9221-97ce03bddfb1
-- title:
--   Actual original full initial right-payment and finite positive simultaneous source-jump chronological HJB budget
-- statement:
--   The genuine original spectrally negative Levy controlled reserve gives a chronological full finite-grid upper bound for the time-zero postpayment value and the initial Stieltjes dividend atom, followed by the discounted value drops and physical right-dividend atoms at any selected strictly positive pre-ruin times with simultaneous source negative jumps. The bound is exactly initial w(x) plus the original source-only discounted jump changes; no initial atom is lost or positive-time ruin payment invented.
-- source:
--   Exact Proved initial original physical right dividend atom 0315346e and positive-time source/payment chronological finite grid d3071eac; additive inequality under canonical hjump.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_source_and_dividend_finite_grid_discounted_jump_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_initial_plus_positive_clock_finite_all_atomic_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : Finset ℝ≥0)
    (hTimes : ∀ t ∈ S, 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∑ t ∈ S,
        (Real.exp (-(q * (t : ℝ))) *
          ((w (x + X.X t ω - rightLimit D t ω) -
              w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t -
                D t ω)) +
            (rightLimit D t ω - D t ω)))) ≤
    w x + (∑ t ∈ S,
      (Real.exp (-(q * (t : ℝ))) *
        (w (x + X.X t ω - D t ω) -
          w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)))) := by sorry
