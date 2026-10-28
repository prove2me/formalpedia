-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_true_capital_transform_antitone
-- name    : AvramDividend.Classical.chat04_esscher_true_capital_transform_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:31:47.49392+00:00
-- url     : https://prove2.me/theorems/a8f01e9a-f1d0-4283-940c-11325b803da5
-- title:
--   Actual Esscher-weighted killed survival capital transform decreases with time
-- statement:
--   The true capital-integrated discounted Esscher mass of paths that avoid ruin through a horizon decreases as the horizon increases. Both the initial-capital exponential weight and the terminal compensated Lévy exponential occur inside the genuine killed path integral.
-- source:
--   Combine Proved capital-factor-out lemma and Proved capital-integrated nonnegative mass antitonicity. This establishes the true original-measure finite-horizon Wiener-Hopf scalar transform as an antitone family, paving the way for monotone convergence without invoking the unproved two-sided exit or killed-scale harmonicity identities.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_capital_weight_inside_lintegral
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_capital_laplace_horizon_antitone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_true_capital_transform_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ β : ℝ) (hθ : 0 ≤ θ) (hβ : 0 < β)
    (t u : ℝ≥0) (htu : t ≤ u) :
    (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-β * x) *
              Real.exp (θ * X.X u ω -
                (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P
      ∂volume) ≤
    (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-β * x) *
              Real.exp (θ * X.X t ω -
                (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P
      ∂volume) := by sorry
