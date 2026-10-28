-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_esscher_weight_pointwise_time_split
-- name    : AvramDividend.Classical.killed_esscher_weight_pointwise_time_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:05:57.79102+00:00
-- url     : https://prove2.me/theorems/45a898a9-b7ef-4dae-8481-12615b12679d
-- title:
--   Exact pathwise factorisation of continuously killed Esscher weights at a fixed time
-- statement:
--   The compensated Esscher exponential killed by one-sided survival through s+u equals the product of its survival-killed value at s and the future-increment Esscher exponential killed by survival during [s,s+u] from the observed reserve. This holds pointwise for any sample path, with both endpoints and all intervening times included.
-- source:
--   Composition of the accepted multiplicative Esscher exponential lemma and the exact past/future pathwise lower-survival event split, using set indicators. Next direct input to the finite-horizon killed Markov identity.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_esscher_compensated_exp_time_split
import Theorems.Thm_AvramDividend_Classical_lower_survival_future_increment_pathwise_split

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_esscher_weight_pointwise_time_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (x : ℝ) (s u : ℝ≥0) (ω : Ω) :
    ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp
        (θ * X.X (s + u) ω -
          ((s + u : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω =
    (({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp
        (θ * X.X s ω -
          (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω) *
    (({ω | ∀ v : ℝ≥0, v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)}).indicator
      (fun ω => Real.exp
        (θ * (X.X (s + u) ω - X.X s ω) -
          (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω) := by sorry
