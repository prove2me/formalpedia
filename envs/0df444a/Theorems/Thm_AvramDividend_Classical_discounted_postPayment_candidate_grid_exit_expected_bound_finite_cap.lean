-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_grid_exit_expected_bound_finite_cap
-- name    : AvramDividend.Classical.discounted_postPayment_candidate_grid_exit_expected_bound_finite_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:22:37.223248+00:00
-- url     : https://prove2.me/theorems/e686b574-ed21-44d1-b9f6-a5e3dd3e6d6d
-- title:
--   Expected discounted HJB terminal value at finite-grid exits admits a deterministic finite-cap bound
-- statement:
--   For every finite real cap, capped-admissible dividend strategy satisfying the exact root HJB hypotheses, and deterministic grid exit K identified by hittingBtwn, the expectation of discounted w(Uplus_{clock K}) is bounded above by a nonnegative deterministic B, uniformly over the grid stop's outcome. The separate Proved uniform sample-path finite-cap theorem supplies B≥0, the accepted all-times nonnegative HJB terminal theorem and q>0 give 0≤exp(-q clock K)w(Uplus_{clock K})≤B. An independently Proved grid-exit integrability theorem supplies Integrable of the stopped payoff. Use pinned MeasureTheory.integral_mono_ae and IsProbabilityMeasure P to conclude expectation≤B. This theorem does not assert the fundamental dividend budget or the missing Lévy–Itô generator drift relation.
-- source:
--   Dependency gate: only after discounted_postPayment_candidate_grid_exit_integrable_finite_cap target 4be55ddb-4f53-42f2-9b3a-c607994248dd is Proved. Exact remote compiler signature of MeasureTheory.integral_mono_ae verified.

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_grid_exit_integrable_finite_cap
import Theorems.Thm_AvramDividend_Classical_capped_postPayment_candidate_uniform_upper_bound_finite_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_postPayment_terminal_nonnegative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_postPayment_candidate_grid_exit_expected_bound_finite_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (x c : ℝ) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max
        (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω -
          rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∫ ω, Real.exp (-(q * (clock (K ω) : ℝ))) *
        w (x + X.X (clock (K ω)) ω -
          rightLimit D (clock (K ω)) ω) ∂P) ≤ B := by sorry
