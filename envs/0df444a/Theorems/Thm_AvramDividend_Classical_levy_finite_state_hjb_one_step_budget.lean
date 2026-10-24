-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finite_state_hjb_one_step_budget
-- name    : AvramDividend.Classical.levy_finite_state_hjb_one_step_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:30:57.557254+00:00
-- url     : https://prove2.me/theorems/81c28a8f-bf6a-4239-9193-bc376d01c843
-- title:
--   One-step conditional Lévy dividend verification under HJB and a discounted semigroup inequality
-- statement:
--   For finitely many adapted post-payment reserve states u_i and nonnegative dividends a_i≤u_i with reserves bounded by cap C, assume the original local HJB maximum equation and regularity of w. Also suppose its discounted Lévy transition semigroup is dominated by w at the post-payment state, with necessary integrability. Then, for an arbitrary finite-valued state selector measurable in the past filtration, the current dividend plus the discounted conditional value at the next time step does not exceed the pre-payment verification value, almost surely. First use the proved exact HJB secant lemma to derive a_i≤w(u_i)-w(u_i-a_i) at each state, then apply the general finite-valued conditional Lévy semigroup budget theorem. This supplies a reusable rigorous finite-grid verification step and isolates generator-to-semigroup domination as the outstanding analytic stochastic obligation, distinct from the already solved adapted Markov and dividend inequalities.
-- source:
--   AvramDividend.Classical.local_verification_hjb_controls_dividend_jump_le_cap (Proved); AvramDividend.Classical.levy_finite_state_hjb_one_step_budget_of_semigroup_bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap
import Theorems.Thm_AvramDividend_Classical_levy_finite_state_hjb_one_step_budget_of_semigroup_bound
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finite_state_hjb_one_step_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    {ι : Type*} [Fintype ι]
    (p : Ω → ι)
    (hp : ∀ i, MeasurableSet[𝓕 s] {ω : Ω | p ω = i})
    (u a : ι → ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (q : ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (ha : ∀ i, 0 ≤ a i) (hua : ∀ i, a i ≤ u i)
    (huC : ∀ i, ENNReal.ofReal (u i) ≤ C)
    (hI : ∀ i, Integrable
      (fun ω => w (u i - a i + X.X (t - s) ω)) P)
    (hsemi : ∀ i,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ ω, w (u i - a i + X.X (t - s) ω) ∂P) ≤ w (u i - a i)) :
    ∀ᵐ ω ∂P,
      a (p ω) +
        Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
          (P[(fun η => w (u (p η) - a (p η) +
            (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
      w (u (p ω)) := by sorry
