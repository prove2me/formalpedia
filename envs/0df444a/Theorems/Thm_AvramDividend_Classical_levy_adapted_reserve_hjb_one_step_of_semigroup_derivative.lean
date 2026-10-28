-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_adapted_reserve_hjb_one_step_of_semigroup_derivative
-- name    : AvramDividend.Classical.levy_adapted_reserve_hjb_one_step_of_semigroup_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T15:18:15.975571+00:00
-- url     : https://prove2.me/theorems/f177a544-bd07-455f-bcfe-d38e9a6dff5a
-- title:
--   Adapted Lévy HJB one-step dividend bound from differentiable transition expectation
-- statement:
--   Let f_ω(r) be the Lévy transition expectation of the verification payoff starting from the adapted post-dividend reserve u(ω)-a(ω), evaluated at nonnegative time r. Assume f_ω is continuous at zero, differentiable for positive times with derivative bounded above by q f_ω, that its initial value is at most w(u-a), and that its value at t-s equals the corresponding Lévy transition expectation. The proved discounted Grönwall comparison supplies the semigroup domination required by the proved adapted random-reserve one-step HJB bound. This gives a conditional one-step stochastic dividend budget usable in the proved finite-grid expectation telescoping theorem. The outstanding work is to derive the derivative inequality from the stopped Lévy generator/Itô formula, then pass grid bounds to full Stieltjes dividends.

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_levy_discounted_semigroup_le_initial_of_deriv_le
import Theorems.Thm_AvramDividend_Classical_levy_adapted_reserve_hjb_one_step_budget

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_adapted_reserve_hjb_one_step_of_semigroup_derivative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (w : ℝ → ℝ) (hw : Measurable w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable (fun η => w (x + X.X (t - s) η)) P)
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
    (f : Ω → ℝ → ℝ)
    (hf : ∀ᵐ ω ∂P,
      ContinuousOn (f ω) (Ici 0) ∧
      (∀ r : ℝ, 0 < r → DifferentiableAt ℝ (f ω) r) ∧
      (∀ r : ℝ, 0 < r → deriv (f ω) r ≤ q * f ω r) ∧
      f ω 0 ≤ w (u ω - a ω) ∧
      f ω ((t - s : ℝ≥0) : ℝ) =
        (∫ η, w (u ω - a ω + X.X (t - s) η) ∂P)) :
    ∀ᵐ ω ∂P,
      a ω + Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (P[(fun η => w (u η - a η +
          (X.X t η - X.X s η))) | 𝓕 s]) ω ≤
      w (u ω) := by sorry
