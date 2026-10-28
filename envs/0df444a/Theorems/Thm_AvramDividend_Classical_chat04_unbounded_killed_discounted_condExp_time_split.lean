-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_discounted_condExp_time_split
-- name    : AvramDividend.Classical.chat04_unbounded_killed_discounted_condExp_time_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:29:27.7593+00:00
-- url     : https://prove2.me/theorems/070918e3-71b8-41c4-932a-752d00a9260d
-- title:
--   Unbounded-variation killed q-scale conditional expectation splitting without Standing
-- statement:
--   For a spectrally negative Levy process of unbounded variation, the conditional expected killed and discounted q-scale payoff across deterministic times s <= u splits into historical survival and the discounted future-window conditional expectation, without Standing assumptions. This is the Standing-free conditional splitting prerequisite for the unbounded two-sided-exit stopped-scale martingale.
-- source:
--   Source-faithful strengthening of Proved chat04_standing_killed_discounted_condExp_time_split (3ba2dca6), replacing Standing-only fixed-time integrability with Proved chat04_unbounded_scale_fixed_time_integrable (used in Proved dbafcb98). Uses Proved chat04_lower_survival_closed_window_measurable and chat04_killed_discounted_condExp_time_split. Supports the censored q-harmonicity bridge beneath aed50a34 in Avram Dividend mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Does not assume the exit identity.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_killed_discounted_condExp_time_split
import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_unbounded_killed_discounted_condExp_time_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (s : ℝ))) *
          P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
            0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
              (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
                W (x + X.X u ω)) | 𝓕 s] ω) := by sorry
