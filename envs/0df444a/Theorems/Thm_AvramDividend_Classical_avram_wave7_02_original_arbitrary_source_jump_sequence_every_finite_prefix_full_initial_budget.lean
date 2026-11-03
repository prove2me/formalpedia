-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_arbitrary_source_jump_sequence_every_finite_prefix_full_initial_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_arbitrary_source_jump_sequence_every_finite_prefix_full_initial_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:11:13.184108+00:00
-- url     : https://prove2.me/theorems/a14aba30-5332-4732-8efc-8a1797ae2170
-- title:
--   Every finite prefix of arbitrary original source-before-dividend jump sequence satisfies full time-zero HJB budget without summability
-- statement:
--   For actual original spectrally negative source negative jumps, arbitrary enumerated pre-ruin and closed-cap source marks have a uniform pathwise discounted source-before-payment HJB budget over every finite prefix. The complete initial right-payment Stieltjes atom is included. No summability, injectivity or convergence hypothesis is imposed on the enumeration. Retains the genuine original X and controlled D; a full stochastic stopped Ito and clock compensation remain necessary.
-- source:
--   Compose proved original time-zero Stieltjes HJB value-drop, negative source all-crossings C1 monotonicity and simultaneous original right-payment jump value budget, using finite prefix sum_nonpos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_clock_source_and_payment_simultaneous_jump_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_arbitrary_source_jump_sequence_every_finite_prefix_full_initial_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v < 0, w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℕ → ℝ≥0)
    (hTimes : ∀ n, 0 < t n ∧ (t n : ℝ≥0∞) < ruinTime X x D ω)
    (hValid : ∀ n,
      X.X (t n) ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) ∧
      0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) - D (t n) ω ∧
      ENNReal.ofReal
        (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) - D (t n) ω) ≤ C) :
    let J : ℕ → ℝ := fun i =>
      Real.exp (-(q * (t i : ℝ))) *
        ((w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t i) -
              D (t i) ω)) +
          (rightLimit D (t i) ω - D (t i) ω))
    ∀ n : ℕ, (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n, J i) ≤ w x := by sorry
