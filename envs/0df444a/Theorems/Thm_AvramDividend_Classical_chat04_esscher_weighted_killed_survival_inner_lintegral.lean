-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_killed_survival_inner_lintegral
-- name    : AvramDividend.Classical.chat04_esscher_weighted_killed_survival_inner_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:50:25.25933+00:00
-- url     : https://prove2.me/theorems/9eabdd76-b38c-4c92-bc21-f8bbb12f2278
-- title:
--   Finite-horizon Esscher-weighted nonnegative capital Laplace envelope
-- statement:
--   At fixed finite horizon and Lévy path, the initial-capital nonnegative Laplace integral killed at ruin and multiplied by the terminal Esscher exponential equals the positive reflected-running-infimum envelope times the same Esscher weight. This is the ENNReal form compatible with Tonelli.
-- source:
--   Extend Proved killed_survival_inner_lintegral_envelope (09e06fab) by pulling the measurable path-constant Esscher ENNReal factor out of the capital lintegral. The survival region is Borel from the proved finite-horizon running-infimum equivalence. No killed-scale harmonicity or exit identity is assumed.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_killed_survival_inner_lintegral_envelope

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_killed_survival_inner_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) (β θ : ℝ) (hβ : 0 < β) :
    (∫⁻ (x : ℝ),
      Set.indicator
        {y : ℝ | 0 < y ∧ ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}
        (fun y => ENNReal.ofReal
          (Real.exp (-β * y) *
            Real.exp (θ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) x ∂volume) =
    ENNReal.ofReal
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
    ENNReal.ofReal
      (Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) := by sorry
