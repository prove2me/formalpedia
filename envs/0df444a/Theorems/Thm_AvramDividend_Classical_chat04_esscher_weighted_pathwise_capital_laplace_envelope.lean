-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_pathwise_capital_laplace_envelope
-- name    : AvramDividend.Classical.chat04_esscher_weighted_pathwise_capital_laplace_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:42:38.742682+00:00
-- url     : https://prove2.me/theorems/fea76d26-9072-4bbd-a968-7d6ed900ff12
-- title:
--   Pathwise Esscher-weighted killed-survival capital Laplace envelope
-- statement:
--   Multiplying the finite-horizon one-sided killed-survival capital Laplace integral by the Esscher exponential at a fixed sample path yields the reflected-running-infimum envelope times that weight. This is the pathwise integrand identity for the Esscher-weighted Laplace/Tonelli transform.
-- source:
--   Imports the already Proved all-paths killed-survival capital Laplace envelope. The Esscher factor is constant in initial capital and pulls outside its real integral. A necessary scalar input for the positive-root Wiener-Hopf transform, independent of two-sided-exit identities.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_pathwise_killed_survival_laplace_envelope_all_paths

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_pathwise_capital_laplace_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) (β θ : ℝ) (hβ : 0 < β) :
    (∫ x in {x : ℝ | 0 < x ∧
        ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω},
      Real.exp (-β * x) *
        Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) =
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
        Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) := by sorry
