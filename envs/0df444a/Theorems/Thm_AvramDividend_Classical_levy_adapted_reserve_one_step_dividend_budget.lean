-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_adapted_reserve_one_step_dividend_budget
-- name    : AvramDividend.Classical.levy_adapted_reserve_one_step_dividend_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:21:57.199861+00:00
-- url     : https://prove2.me/theorems/3c9074bf-6590-4bb7-9597-2d55cca3b19f
-- title:
--   Conditional one-step dividend verification for an arbitrary integrable adapted reserve with Lipschitz candidate value
-- statement:
--   Let u and a be arbitrary random pre-payment reserve and immediate dividend, with their difference Z=u-a measurable in the past filtration and integrable. Suppose w is a measurable Lipschitz candidate with the integrability and simple-approximation requirements of the proved general Lévy conditional Markov theorem. If almost surely the current dividend a is bounded by the w-value decrease across payment, and almost surely the discounted deterministic Lévy transition expectation starting at Z is bounded by w(Z), then the immediate dividend plus discounted conditional expectation of the future candidate after the Lévy increment is at most the pre-payment candidate w(u), almost surely. This extends finite-state one-step verification to genuinely random adapted reserves, isolating semigroup dominance and secant estimates from the already proved conditional Lévy Markov property.
-- source:
--   Proved AvramDividend.Classical.levy_increment_condExp_integrable_adapted_reserve_lipschitz (06df99a9-8ded-4440-9721-3829f15f2067), with almost-sure HJB secant and semigroup bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_integrable_adapted_reserve_lipschitz
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_adapted_reserve_one_step_dividend_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (w : ℝ → ℝ) (hw : Measurable w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable
      (fun η => w (x + X.X (t - s) η)) P)
    (u a : Ω → ℝ) (q : ℝ)
    (hZ : Measurable[𝓕 s] (fun ω => u ω - a ω))
    (hZm : Measurable (fun ω => u ω - a ω))
    (hZI : Integrable (fun ω => u ω - a ω) P)
    (hZPay : Integrable
      (fun ω => w (u ω - a ω + (X.X t ω - X.X s ω))) P)
    (hSPay : ∀ n : ℕ, Integrable (fun ω =>
      w ((SimpleFunc.approxOn (fun η => u η - a η) hZm
        (Set.range (fun η => u η - a η) ∪ {0}) 0
        (by simp) n) ω + (X.X t ω - X.X s ω))) P)
    (hsec : ∀ᵐ ω ∂P, a ω ≤ w (u ω) - w (u ω - a ω))
    (hsemi : ∀ᵐ ω ∂P,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ η, w (u ω - a ω + X.X (t - s) η) ∂P) ≤ w (u ω - a ω)) :
    ∀ᵐ ω ∂P,
      a ω + Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
          (P[(fun η => w (u η - a η +
            (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
      w (u ω) := by sorry
