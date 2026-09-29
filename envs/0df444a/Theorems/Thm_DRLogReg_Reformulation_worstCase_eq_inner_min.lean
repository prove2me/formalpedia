-- Prove2me | Theorems.Thm_DRLogReg_Reformulation_worstCase_eq_inner_min
-- name    : DRLogReg.Reformulation.worstCase_eq_inner_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:35:00.528415+00:00
-- url     : https://prove2.me/theorems/832100c2-d8cc-42ac-befa-70b62678aa17
-- title:
--   Theorem 1, for fixed β — the worst-case expected logloss equals the inner minimum of (7)
-- statement:
--   Let $V$ be a finite-dimensional real normed space with any norm $\|\cdot\|$ and dual norm $\|\cdot\|_*$, let $\kappa>0$, $\varepsilon\ge0$, and let $(\hat x_i,\hat y_i)_{i=1}^N$ be training samples with $N\ge1$. For every weight $\beta$,
--   $$\sup_{\mathbb Q\in\mathbb B_\varepsilon(\hat{\mathbb P}_N)}\mathbb E^{\mathbb Q}\big[l_\beta(x,y)\big] \;=\; \min_{\lambda,\,s}\Big\{\lambda\varepsilon+\frac1N\sum_{i=1}^N s_i \;:\; l_\beta(\hat x_i,\hat y_i)\le s_i,\ l_\beta(\hat x_i,-\hat y_i)-\lambda\kappa\le s_i\ (i\le N),\ \|\beta\|_*\le\lambda\Big\},$$
--   and the minimum on the right is attained.
--
--   This is the per-$\beta$ form of Theorem 1: taking the infimum over $\beta$ on both sides gives the identity between the optimal values of (6) and (7). It turns an optimization over an infinite-dimensional set of distributions into a finite convex program in $(\lambda, s)$.
--
--   **Formalization Note.** The left side is computed in $[0,\infty]$ and the statement asserts it equals the (finite) minimum $v$, which is stated as the least element of the set of objective values of the feasible $(\lambda,s)$.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 4, Theorem 1, eq. (7) (for fixed β)

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.Reformulation

/-- Theorem 1 for a fixed `β`, Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, *Distributionally Robust Logistic Regression*,
NIPS 2015, p. 4, eq. (7).

For every weight `β`, the worst-case expected logloss `sup_{Q ∈ B_ε(P̂_N)} E^Q[l_β(x, y)]`
equals the minimum over `(λ, s)` of `λε + (1/N) ∑ s_i` subject to the constraints of (7) with
this `β` held fixed; the minimum is attained, for every `ε ≥ 0`. -/
theorem worstCase_eq_inner_min
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (β : V →L[ℝ] ℝ) :
    ∃ v : ℝ, IsLeast ((fun q : ℝ × (Fin N → ℝ) => objective7 ε (β, q)) ''
        {q | (β, q) ∈ feasible7 κ xhat yhat}) v ∧
      worstCase κ ε xhat yhat β = ENNReal.ofReal v := by sorry

end DRLogReg.Reformulation
