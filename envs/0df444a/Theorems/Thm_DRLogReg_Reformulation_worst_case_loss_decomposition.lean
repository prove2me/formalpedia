-- Prove2me | Theorems.Thm_DRLogReg_Reformulation_worst_case_loss_decomposition
-- name    : DRLogReg.Reformulation.worst_case_loss_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:35:31.285217+00:00
-- url     : https://prove2.me/theorems/2c25eb76-3cf9-4f8b-9297-abc868133fa7
-- title:
--   Remark 2, Eq. (9) — the worst-case loss splits into λ̂ε, the empirical logloss and a label-uncertainty term
-- statement:
--   Let $V$ be a finite-dimensional real normed space with any norm, $\kappa>0$, $\varepsilon\ge0$, and $(\hat x_i,\hat y_i)_{i=1}^N$ training samples with $N\ge1$. Suppose $(\hat\beta,\hat\lambda,\hat s)$ is an optimal solution of program (7), and let $\hat J$ be the optimal value of (7). Then
--   $$\hat J = \hat\lambda\varepsilon + \mathbb E^{\hat{\mathbb P}_N}\big[l_{\hat\beta}(x,y)\big] + \frac1N\sum_{i=1}^N\max\big\{0,\ \hat y_i\langle\hat\beta,\hat x_i\rangle-\hat\lambda\kappa\big\},$$
--   where $\mathbb E^{\hat{\mathbb P}_N}[l_{\hat\beta}(x,y)] = \frac1N\sum_{i=1}^N l_{\hat\beta}(\hat x_i,\hat y_i)$ is the empirical logloss on the training set.
--
--   The last term is a regularizer, absent from standard regularized logistic regression, that accounts for label uncertainty and decreases in $\kappa$.
--
--   **Formalization Note.** The optimal value $\hat J$ is the infimum of the objective of (7) over its feasible set, taken in $[0,\infty]$; the identity is stated there. The empirical expectation is written directly as the sample average. When (7) has no optimal solution the hypothesis cannot be met; for $\varepsilon>0$ an optimal solution always exists (Theorem 1).
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 4, Remark 2, eq. (9)

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.Reformulation

/-- Remark 2 (Worst-Case Loss), Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, *Distributionally Robust Logistic Regression*,
NIPS 2015, p. 4, eq. (9).

If `(β̂, λ̂, ŝ)` is an optimal solution of program (7), then the optimal value `Ĵ` of (7) is
`Ĵ = λ̂ε + E^{P̂_N}[l_β̂(x, y)] + (1/N) ∑ max{0, ŷ_i⟨β̂, x̂_i⟩ − λ̂κ}`,
where the empirical expected logloss `E^{P̂_N}[l_β̂]` is written as the sample average
`(1/N) ∑ l_β̂(x̂_i, ŷ_i)`. -/
theorem worst_case_loss_decomposition
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool)
    (βhat : V →L[ℝ] ℝ) (lamhat : ℝ) (shat : Fin N → ℝ)
    (hfeas : (βhat, lamhat, shat) ∈ feasible7 κ xhat yhat)
    (hopt : ∀ q ∈ feasible7 κ xhat yhat, objective7 ε (βhat, lamhat, shat) ≤ objective7 ε q) :
    value7 κ ε xhat yhat =
      ENNReal.ofReal (lamhat * ε + (N : ℝ)⁻¹ * ∑ i, logloss βhat (xhat i) (yhat i) +
        (N : ℝ)⁻¹ * ∑ i, max 0 (sgn (yhat i) * βhat (xhat i) - lamhat * κ)) := by sorry

end DRLogReg.Reformulation
