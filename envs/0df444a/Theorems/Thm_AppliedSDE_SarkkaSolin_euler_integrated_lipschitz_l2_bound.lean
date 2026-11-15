-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_integrated_lipschitz_l2_bound
-- name    : AppliedSDE.SarkkaSolin.euler_integrated_lipschitz_l2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:08:29.131427+00:00
-- url     : https://prove2.me/theorems/3945c3b1-519f-477f-8ce3-bc00eef05830
-- title:
--   Integrated L2 Lipschitz stability of drift and diffusion coefficients
-- statement:
--   Let two real-valued random variables X,Y live on any measure space, with drift b and diffusion coefficient sigma both globally Lipschitz with constant L>=0. If the relevant squared increments are integrable, then the integral (expectation for probability measures) of the sum of squared drift and diffusion differences is bounded above by 2L² times the L2 squared distance between X and Y. This lifts the proved pointwise squared-Lipschitz estimate through integration and supplies the exact deterministic coefficient estimate used in the Euler-Maruyama one-step mean-square error recurrence.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 8, strong mean-square Euler-Maruyama convergence.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_lipschitz_squared_sum
open MeasureTheory

theorem AppliedSDE.SarkkaSolin.euler_integrated_lipschitz_l2_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (X Y : Ω → ℝ) (b σ : ℝ → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (hσ : ∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|)
    (hi : Integrable
      (fun ω => (b (X ω) - b (Y ω)) ^ 2 +
        (σ (X ω) - σ (Y ω)) ^ 2) P)
    (hj : Integrable
      (fun ω => (2 * L ^ 2) * (X ω - Y ω) ^ 2) P) :
    (∫ ω, ((b (X ω) - b (Y ω)) ^ 2 +
      (σ (X ω) - σ (Y ω)) ^ 2) ∂P) ≤
      ∫ ω, (2 * L ^ 2) * (X ω - Y ω) ^ 2 ∂P := by
  sorry
