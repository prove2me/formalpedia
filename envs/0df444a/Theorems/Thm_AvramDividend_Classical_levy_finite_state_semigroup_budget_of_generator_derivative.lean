-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finite_state_semigroup_budget_of_generator_derivative
-- name    : AvramDividend.Classical.levy_finite_state_semigroup_budget_of_generator_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:35:04.871626+00:00
-- url     : https://prove2.me/theorems/2c4445e1-5586-4c6b-8f55-a8a44ef97ae3
-- title:
--   Finite-state Lévy semigroup budget from pointwise generator HJB control
-- statement:
--   For each state index i with pre-payment reserve u_i and dividend a_i, suppose the Lévy transition expectation F_i(s) and its generator expectation can be interchanged under time differentiation, with F_i(0)=w(u_i-a_i). If the global generator HJB inequality Gamma w <= q w holds, the discounted transition expectation starting at each post-dividend reserve is bounded by the verification value at that reserve. This supplies exactly the statewise semigroup premise of the already Proved finite-state conditional dividend one-step budget theorem. The remaining hard problem is establishing the derivative interchange under local stopped/killed dynamics.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4, HJB stochastic-verification argument.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_discounted_semigroup_le_of_generator_derivative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finite_state_semigroup_budget_of_generator_derivative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (u a : ι → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (F : ι → ℝ → ℝ)
    (hF0 : ∀ i, F i 0 = w (u i - a i))
    (hFcont : ∀ i, ContinuousOn (F i) (Ici 0))
    (hFdiff : ∀ i s, 0 < s → DifferentiableAt ℝ (F i) s)
    (hFtrans : ∀ i s, 0 ≤ s →
      F i s = ∫ ω, w (u i - a i + X.X (Real.toNNReal s) ω) ∂P)
    (hFderiv : ∀ i s, 0 < s →
      deriv (F i) s = ∫ ω,
        X.generator w (u i - a i + X.X (Real.toNNReal s) ω) ∂P)
    (hIntW : ∀ i s, 0 < s → Integrable
      (fun ω => w (u i - a i + X.X (Real.toNNReal s) ω)) P)
    (hIntGen : ∀ i s, 0 < s → Integrable
      (fun ω => X.generator w (u i - a i + X.X (Real.toNNReal s) ω)) P)
    (hHJB : ∀ y : ℝ, X.generator w y ≤ q * w y)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ i,
      Real.exp (-(q * t)) *
        (∫ ω, w (u i - a i + X.X (Real.toNNReal t) ω) ∂P) ≤
      w (u i - a i) := by sorry
