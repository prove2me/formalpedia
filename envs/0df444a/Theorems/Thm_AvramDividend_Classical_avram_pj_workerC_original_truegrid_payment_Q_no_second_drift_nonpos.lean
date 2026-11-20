-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_truegrid_payment_Q_no_second_drift_nonpos
-- name    : AvramDividend.Classical.avram_pj_workerC_original_truegrid_payment_Q_no_second_drift_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:54:06.419699+00:00
-- url     : https://prove2.me/theorems/e8d9b96d-f557-45a8-bfc6-b9e1a32829e0
-- title:
--   Original true ruin-clipped finite payment mesh correction nonpositive with HJB drift appearing only once
-- statement:
--   For every original subordinate ruin-clipped physical grid the discounted sum of all pre-ruin right dividend cash minus the exact right-value drop is nonpositive. It contains only payment corrections; no duplicate generator drift B.
-- source:
--   Independent sign input for Worker C genuine infinite-activity pure-jump physical Ito signed source d34cb09a and original W/Iio cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_strict_grid_dividend_points_pre_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_truegrid_payment_Q_no_second_drift_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (k : ℕ) (ω : Ω) :
    let mesh : Finset ℝ≥0 :=
      ((Finset.range (k + 1)).image
        (fun i : ℕ => min
          ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
          (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)
    (∑ t ∈ mesh, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) -
      (w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
        (rightLimit D t ω - D t ω))))) ≤ 0 := by sorry
