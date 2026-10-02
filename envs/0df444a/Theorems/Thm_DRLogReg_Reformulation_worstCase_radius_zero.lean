-- Prove2me | Theorems.Thm_DRLogReg_Reformulation_worstCase_radius_zero
-- name    : DRLogReg.Reformulation.worstCase_radius_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:34:29.858005+00:00
-- url     : https://prove2.me/theorems/7199ebad-0126-4e61-b98a-76e32c0635f0
-- title:
--   §2, p. 3 — with ε = 0 the robust objective (6) is the average logloss (2)
-- statement:
--   Let $V$ be a finite-dimensional real normed space with any norm, $\kappa > 0$, and $(\hat x_i,\hat y_i)_{i=1}^N$ training samples with $N\ge1$ and empirical distribution $\hat{\mathbb P}_N$. For every weight $\beta$, the worst-case expected logloss over the Wasserstein ball of radius $0$ equals the empirical average logloss:
--   $$\sup_{\mathbb Q\in\mathbb B_0(\hat{\mathbb P}_N)}\mathbb E^{\mathbb Q}\big[l_\beta(x,y)\big] = \frac1N\sum_{i=1}^N l_\beta(\hat x_i,\hat y_i).$$
--
--   Consequently the distributionally robust problem (6) with $\varepsilon = 0$ has the same objective, hence the same optimal value and minimizers, as the maximum-likelihood problem (2) of classical logistic regression.
--
--   **Formalization Note.** The ball, the Wasserstein distance and the expectations are in $[0,\infty]$; labels are `Bool` embedded as $\pm1$.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 3, §2 (sentence after eq. (6))

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.Reformulation

/-- §2, p. 3 (Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, *Distributionally Robust Logistic Regression*,
NIPS 2015): "(6) reduces to the average logloss minimization problem (2) associated
with classical logistic regression if we set ε = 0". For every weight `β`, the worst-case
expected logloss over the Wasserstein ball of radius `0` around `P̂_N` equals the empirical
average logloss `(1/N) ∑ l_β(x̂_i, ŷ_i)`, so the objectives of (6) and (2) coincide. -/
theorem worstCase_radius_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (β : V →L[ℝ] ℝ) :
    worstCase κ 0 xhat yhat β =
      ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, logloss β (xhat i) (yhat i)) := by sorry

end DRLogReg.Reformulation
