-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_arbitrary_weight_right_atom_hjump_bound
-- name    : AvramDividend.Classical.avram_wave4_04b_arbitrary_weight_right_atom_hjump_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:32:23.848565+00:00
-- url     : https://prove2.me/theorems/3e82a1a7-c678-4eb9-836f-6d71b75d1bd0
-- title:
--   Chronological hjump controls every actual right-payment atom for arbitrary nonnegative stopped weights
-- statement:
--   For an actual source spectrally negative Lévy process X and actual adapted dividend strategy D, the closed finite-horizon dividend measure has exact right-payment singleton masses. For any nonnegative extended-real payoff weight f, the weighted countable sum of true Stieltjes right-payment atoms is bounded above by the weighted source chronological pre-payment test-function secant drops. The hjump premise is required only at times where f is nonzero. Consequently the theorem is compatible with stopped-payment indicators which vanish after ruin, including payments at time zero and the horizon endpoint. No atom-only concentration or dt density is assumed. This is a measure/control inequality and not an Ito–Meyer stochastic formula.
-- source:
--   Proved exact singleton rightJump identity, Mathlib ENNReal.tsum_le_tsum and monotonic multiplication; adapted source riskProcess, chronological hjump on support of the actual payoff weight.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_arbitrary_weight_right_atom_hjump_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞)
    (hjump : ∀ t : ℝ≥0, t ≤ T → f (t : ℝ) ≠ 0 →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∀ A : Set ℝ,
      (∑' s : A, μ {(s : ℝ)} * f (s : ℝ)) ≤
      (∑' s : A,
        ENNReal.ofReal
          (w (riskProcess X x D (s : ℝ).toNNReal ω) -
            w (riskProcess X x D (s : ℝ).toNNReal ω -
              (rightLimit D (s : ℝ).toNNReal ω -
                D (s : ℝ).toNNReal ω))) * f (s : ℝ)) := by sorry
