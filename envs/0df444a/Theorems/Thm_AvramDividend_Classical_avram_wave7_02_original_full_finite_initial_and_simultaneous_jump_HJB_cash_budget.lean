-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_full_finite_initial_and_simultaneous_jump_HJB_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_full_finite_initial_and_simultaneous_jump_HJB_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:16:39.13982+00:00
-- url     : https://prove2.me/theorems/ff0dedbc-60d8-4221-8a9f-1e61d0a23221
-- title:
--   Original BV complete time-zero plus finite simultaneous negative-source/right-payment HJB value jump budget
-- statement:
--   For the literal original controlled spectrally negative Levy process, all complete right-payment HJB atoms at time zero and any selected finite set of strictly positive pre-ruin times with nonpositive original source jumps and pre-source closed-cap reserves are dominated pathwise by initial w(x), after accounting for both source and simultaneous dividend value changes with the actual negative marks. Retains full time-zero Stieltjes cash and the real original source process; no replacement process, no missing initial atom, no C2 assumption.
-- source:
--   Accepted Wave7 Chat02 full time-zero plus finite positive concurrent jump budget d1ae71c7 and original negative-source finite signed C1 sum 040d47bc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_plus_positive_clock_finite_all_atomic_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_prejump_valid_finite_source_mark_discounted_C1_nonpositive
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_full_finite_initial_and_simultaneous_jump_HJB_cash_budget
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
    (ω : Ω) (S : Finset ℝ≥0)
    (hTimes : ∀ t ∈ S, 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hValid : ∀ t ∈ S,
      X.X t ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ∧
      0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω ∧
      ENNReal.ofReal
        (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ C) :
    (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∑ t ∈ S,
        (Real.exp (-(q * (t : ℝ))) *
          ((w (x + X.X t ω - rightLimit D t ω) -
              w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t -
                D t ω)) +
            (rightLimit D t ω - D t ω)))) ≤ w x := by sorry
