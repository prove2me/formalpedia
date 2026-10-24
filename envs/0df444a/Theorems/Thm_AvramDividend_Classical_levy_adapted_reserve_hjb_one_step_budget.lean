-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_adapted_reserve_hjb_one_step_budget
-- name    : AvramDividend.Classical.levy_adapted_reserve_hjb_one_step_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:36:34.57252+00:00
-- url     : https://prove2.me/theorems/2dc41b69-90be-41c5-8a56-f6b2270ac1c7
-- title:
--   One-step HJB dividend verification for arbitrary adapted random reserve under semigroup domination
-- statement:
--   Assume the original capped local verification HJB maximum equation for w and a measurable globally Lipschitz candidate payoff. Let an arbitrary past-adapted post-dividend random reserve Z=u-a be integrable, with almost sure nonnegative dividends bounded by reserve u≤C, and suitable payoff/simple-approximation integrability. If the discounted Lévy transition of w from Z does not exceed w(Z) almost surely, then the dividend at time s plus discounted conditional expected future candidate at t is bounded by the pre-payment verification value w(u) almost surely. The proved HJB secant theorem establishes the dividend-value drop inequality, and the separate proved conditional Markov one-step lemma handles arbitrary adapted reserves. The remaining semigroup domination hypothesis is explicit because the local generator inequality alone requires stopped Dynkin/localisation to imply it; this theorem does not silently assume or conclude global q-excessivity.
-- source:
--   Proved local_verification_hjb_controls_dividend_jump_le_cap and levy_adapted_reserve_one_step_dividend_budget; one-step HJB stochastic control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap
import Theorems.Thm_AvramDividend_Classical_levy_adapted_reserve_one_step_dividend_budget
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_adapted_reserve_hjb_one_step_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (w : ℝ → ℝ) (hw : Measurable w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable
      (fun η => w (x + X.X (t - s) η)) P)
    (u a : Ω → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (ha : ∀ᵐ ω ∂P, 0 ≤ a ω)
    (hua : ∀ᵐ ω ∂P, a ω ≤ u ω)
    (huC : ∀ᵐ ω ∂P, ENNReal.ofReal (u ω) ≤ C)
    (hZ : Measurable[𝓕 s] (fun ω => u ω - a ω))
    (hZm : Measurable (fun ω => u ω - a ω))
    (hZI : Integrable (fun ω => u ω - a ω) P)
    (hZPay : Integrable
      (fun ω => w (u ω - a ω + (X.X t ω - X.X s ω))) P)
    (hSPay : ∀ n : ℕ, Integrable (fun ω =>
      w ((SimpleFunc.approxOn (fun η => u η - a η) hZm
        (Set.range (fun η => u η - a η) ∪ {0}) 0
        (by simp) n) ω + (X.X t ω - X.X s ω))) P)
    (hsemi : ∀ᵐ ω ∂P,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ η, w (u ω - a ω + X.X (t - s) η) ∂P) ≤ w (u ω - a ω)) :
    ∀ᵐ ω ∂P,
      a ω + Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
          (P[(fun η => w (u η - a η +
            (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
      w (u ω) := by sorry
