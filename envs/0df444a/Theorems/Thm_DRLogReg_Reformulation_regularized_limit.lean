-- Prove2me | Theorems.Thm_DRLogReg_Reformulation_regularized_limit
-- name    : DRLogReg.Reformulation.regularized_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:36:00.853235+00:00
-- url     : https://prove2.me/theorems/4259914d-7500-41f4-824d-e0b0a35896af
-- title:
--   Remark 1 — as κ → ∞ the optimal value of (7) tends to that of dual-norm-regularized logistic regression
-- statement:
--   Let $V$ be a finite-dimensional real normed space with any norm $\|\cdot\|$ and dual norm $\|\cdot\|_*$, let $\varepsilon\ge0$, and let $(\hat x_i,\hat y_i)_{i=1}^N$ be training samples with $N\ge1$. Write $J_7(\kappa)$ for the optimal value of program (7) with label weight $\kappa$. Then
--   $$\lim_{\kappa\to\infty} J_7(\kappa) \;=\; \inf_\beta\ \varepsilon\|\beta\|_* + \frac1N\sum_{i=1}^N l_\beta(\hat x_i,\hat y_i).$$
--
--   The right side is the regularized logistic regression problem: the regularizer is the dual norm of the norm on the feature space, and the regularization coefficient is the radius $\varepsilon$ of the Wasserstein ball. This gives a distributionally robust interpretation of norm-regularized logistic regression.
--
--   **Formalization Note.** Only the convergence of optimal values is stated; the metric with $\kappa=\infty$ (which the paper also discusses) is not formalized. Optimal values are in $[0,\infty]$ and the limit is along $\kappa\to+\infty$ in $\mathbb R$.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 4, Remark 1

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.Reformulation

/-- Remark 1 (Regularized Logistic Regression), Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, *Distributionally Robust Logistic Regression*,
NIPS 2015, p. 4.

As `κ → ∞`, the optimal value of program (7) converges to the optimal value of the regularized
logistic regression problem `inf_β ε‖β‖_* + (1/N) ∑ l_β(x̂_i, ŷ_i)`, whose regularizer is the
dual norm (the operator norm of `β`) and whose coefficient is the radius `ε`. Only the limit of
the optimal values is formalized; the metric with `κ = ∞` is not. -/
theorem regularized_limit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) :
    Filter.Tendsto (fun κ : ℝ => value7 κ ε xhat yhat) Filter.atTop
      (nhds (⨅ β : V →L[ℝ] ℝ,
        ENNReal.ofReal (ε * ‖β‖ + (N : ℝ)⁻¹ * ∑ i, logloss β (xhat i) (yhat i)))) := by sorry

end DRLogReg.Reformulation
