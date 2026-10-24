-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finite_state_hjb_one_step_budget_of_semigroup_bound
-- name    : AvramDividend.Classical.levy_finite_state_hjb_one_step_budget_of_semigroup_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:15:20.924976+00:00
-- url     : https://prove2.me/theorems/5be9063f-100d-4c59-9e23-2deb0eeb06cd
-- title:
--   One-step conditional dividend verification for an arbitrary payoff on finitely many adapted Lévy reserve states
-- statement:
--   At deterministic times s≤t, let a finite-valued reserve index p be measurable in the past filtration. For each state i, a dividend a_i is bounded by the loss w(u_i)-w(u_i-a_i) of a general candidate value function w, and the discounted deterministic Lévy transition expectation starting at u_i-a_i is bounded by w(u_i-a_i). Then the dividend paid immediately plus the discounted conditional expectation of w evaluated at the post-dividend reserve plus the Lévy increment from s to t is at most w(u_{p(ω)}) almost surely. Apply the already proved finite-valued conditional Markov/Lévy identity to substitute the conditional expectation with the deterministic state-indexed transition expectation, then combine the secant and semigroup inequalities. This proves the substantive adapted one-step step used in a discrete-grid verification alternative without assuming any purely atomic continuous-time dividend measure.
-- source:
--   Proved AvramDividend.Classical.levy_increment_condExp_finite_valued_reserve (cbd1ef08-c269-4698-9126-2f4a4877d524); HJB verification semigroup method.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_finite_valued_reserve
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finite_state_hjb_one_step_budget_of_semigroup_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    {ι : Type*} [Fintype ι]
    (p : Ω → ι)
    (hp : ∀ i, MeasurableSet[𝓕 s] {ω : Ω | p ω = i})
    (u a : ι → ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (q : ℝ)
    (hI : ∀ i, Integrable
      (fun ω => w (u i - a i + X.X (t - s) ω)) P)
    (hsec : ∀ i, a i ≤ w (u i) - w (u i - a i))
    (hsemi : ∀ i,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ ω, w (u i - a i + X.X (t - s) ω) ∂P) ≤ w (u i - a i)) :
    ∀ᵐ ω ∂P,
      a (p ω) +
        Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
          (P[(fun η => w (u (p η) - a (p η) +
            (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
      w (u (p ω)) := by sorry
