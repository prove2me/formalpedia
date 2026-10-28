-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_lintegral_antitone
-- name    : AvramDividend.Classical.chat04_esscher_killed_survival_lintegral_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:16:56.279626+00:00
-- url     : https://prove2.me/theorems/81888144-8caf-4b87-9269-5e59d3a21947
-- title:
--   True nonnegative killed Esscher mass decreases with time at each starting capital
-- statement:
--   For each starting capital and positive-time ordered horizons, the extended nonnegative integral of the Esscher exponential restricted to all-time lower-survival is antitone. This is a nonnegative-integral version of the accepted martingale survival-mass inequality, ready for Tonelli and monotone integration over initial capital.
-- source:
--   Combine Proved real-to-nonnegative killed Esscher bridge 1ccb6dd6 with Proved real killed Esscher antitone 6335f5be; use pinned ENNReal.ofReal_le_ofReal. This is the pointwise x-ordering required for the horizon-antitone capital transform and limiting Wiener–Hopf analysis.

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_real_to_lintegral
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_antitone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_killed_survival_lintegral_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ)
    (t u : ℝ≥0) (htu : t ≤ u) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (θ * X.X u ω -
            (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) ≤
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (θ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) := by sorry
