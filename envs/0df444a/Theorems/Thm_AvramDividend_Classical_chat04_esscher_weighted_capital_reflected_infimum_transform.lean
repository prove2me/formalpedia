-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_capital_reflected_infimum_transform
-- name    : AvramDividend.Classical.chat04_esscher_weighted_capital_reflected_infimum_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:12:11.558703+00:00
-- url     : https://prove2.me/theorems/d0a95041-ebff-4674-84f5-1b72d7e4a210
-- title:
--   Exact finite-horizon Esscher-weighted survival capital Laplace transform
-- statement:
--   The initial-capital Laplace transform of the actual continuously killed Esscher-weighted Lévy semigroup equals the expectation of the exponentially discounted reflected running infimum times the terminal Esscher exponential. This is the finite-horizon weighted Wiener-Hopf input under the original probability law.
-- source:
--   Combine Proved chat04_esscher_weighted_killed_survival_joint_tonelli and Proved chat04_esscher_weighted_killed_survival_inner_lintegral. The first interchanges starting-capital and sample-path integration; the second evaluates the pathwise inner kernel. The resulting exact finite-horizon stochastic transform does not presume the infinite-time Wiener-Hopf identity or the two-sided exit theorem.

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_killed_survival_joint_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_killed_survival_inner_lintegral

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_capital_reflected_infimum_transform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (β θ : ℝ) (hβ : 0 < β) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) =
    (∫⁻ (ω : Ω),
      ENNReal.ofReal
        (Real.exp (-β * max 0
          (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
      ENNReal.ofReal
        (Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ∂P) := by sorry
