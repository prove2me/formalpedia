-- Prove2me | Theorems.Thm_BoydADMM_ModelFit_feature_split_lasso_zbar_update
-- name    : BoydADMM.ModelFit.feature_split_lasso_zbar_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:36:59.640503+00:00
-- url     : https://prove2.me/theorems/126f8404-692c-48e6-a1b2-a35ffbc7d4fc
-- title:
--   §8.3.1, p. 69 — feature-split lasso: z̄^{k+1} = (b + ρAx̄^{k+1} + ρu^k)/(N + ρ)
-- statement:
--   Let $N\ge1$, $\rho>0$, and $b,\overline{Ax},u\in\mathbb R^m$, where $\overline{Ax}=\overline{Ax}^{k+1}$ is the average of the partial predictors and $u=u^k$ the single scaled dual variable. For the lasso loss $l(w)=\frac12\|w\|_2^2$ the $\bar z$-update of feature-split ADMM minimizes
--   $$\frac12\|N\bar z-b\|_2^2+\frac{N\rho}{2}\|\bar z-\overline{Ax}-u\|_2^2 .$$
--   A point $\bar z\in\mathbb R^m$ minimizes this function if and only if
--   $$\bar z=\frac{1}{N+\rho}\bigl(b+\rho\,\overline{Ax}+\rho\,u\bigr).$$
--
--   This is the closed form that makes the gathering step of the feature-split lasso a single vector operation.
--
--   **Formalization Note** The objective is the $\bar z$-update displayed on p. 68 with the lasso loss $l(w)=\frac12\|w\|_2^2$ of §8.1.1 (p. 62). The statement is an equivalence, so it includes existence and uniqueness. $\overline{Ax}$ is taken as a given vector; how it is formed from the blocks does not matter for this identity.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 69, §8.3.1 (with the z̄-update of p. 68)

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3.1, p. 69: for the lasso loss `l(w) = (1/2)‖w‖₂²`, the feature-split `z̄`-update of p. 68
has the unique solution `z̄ = (b + ρ Ax̄ + ρ u)/(N + ρ)`. -/
theorem feature_split_lasso_zbar_update {N m : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (b Axbar u zb : EuclideanSpace ℝ (Fin m)) :
    IsMinOn (fun z : EuclideanSpace ℝ (Fin m) =>
        1 / 2 * ‖(N : ℝ) • z - b‖ ^ 2 + (N : ℝ) * ρ / 2 * ‖z - Axbar - u‖ ^ 2) Set.univ zb ↔
      zb = (1 / ((N : ℝ) + ρ)) • (b + ρ • Axbar + ρ • u) := by sorry

end BoydADMM.ModelFit
