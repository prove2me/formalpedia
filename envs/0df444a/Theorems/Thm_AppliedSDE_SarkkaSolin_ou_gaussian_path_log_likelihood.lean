-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ou_gaussian_path_log_likelihood
-- name    : AppliedSDE.SarkkaSolin.ou_gaussian_path_log_likelihood
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:45:24.238241+00:00
-- url     : https://prove2.me/theorems/2f175e6c-6b0f-4b12-a4d1-552cc50a7bd7
-- title:
--   Positive Ornstein–Uhlenbeck Gaussian transition likelihood and additive log-loss
-- statement:
--   For λ,q and a strictly positive sampling interval Δ, the Gaussian one-step transition density of an OU process with drift -λx and Brownian variance q has autoregressive factor a=exp(-λΔ) and variance v=q(1-exp(-2λΔ))/(2λ). For a nonempty finite sequence of observed states beginning at a fixed x0, every Gaussian transition density is strictly positive and the negative logarithm of their likelihood product is exactly the sum of transition negative log-densities. This formalises the likelihood factorisation and log-loss calculation in Chapter 11, conditional on the OU transition law from Chapter 6; it does not yet establish that law from the SDE.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   -\log\!\prod_{k=0}^{n-1}\rho_k=\sum_{k=0}^{n-1}\left(\frac12\log(2\pi v)+\frac{(x_{k+1}-ax_k)^2}{2v}\right)
--   $$
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Example 11.1 and equations (11.3)–(11.4), printed pp. 234–237; OU transition parameters from Chapter 6. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.ou_gaussian_path_log_likelihood
    (rate q Δ : ℝ) (hrate : 0 < rate) (hq : 0 < q) (hΔ : 0 < Δ)
    {n : ℕ} (hn : 0 < n) (x : Fin (n + 1) → ℝ) :
    let a : ℝ := Real.exp (-rate * Δ)
    let v : ℝ := q / (2 * rate) * (1 - Real.exp (-(2 * rate * Δ)))
    let ρ : Fin n → ℝ := fun k =>
      Real.exp (-((x (Fin.succ k) - a * x (Fin.castSucc k)) ^ 2) / (2 * v)) /
        Real.sqrt (2 * Real.pi * v)
    0 < v ∧
      (∀ k : Fin n, 0 < ρ k) ∧
      (-Real.log (∏ k : Fin n, ρ k) =
        ∑ k : Fin n,
          (Real.log (2 * Real.pi * v) / 2 +
            (x (Fin.succ k) - a * x (Fin.castSucc k)) ^ 2 / (2 * v))) := by
  sorry
